import LegendreK6.M2PilotDefinitions
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp

/-! Generated proposals: every bound is checked by Lean, not by trusting Arb. -/
namespace LegendreK6.M2Pilot.Enclosures.Sigma004
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem sigma_factor_upper_512 : sigmaFactor (512 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-666677 / 16384 : ℚ) : ℝ) - Real.exp ((-2607 / 64 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_512 : sigmaPower (512 : Fin 1536) ≤ ((136472715980925 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_513 : sigmaFactor (513 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-625196825 / 15376384 : ℚ) : ℝ) - Real.exp ((-1251735705 / 30752768 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_513 : sigmaPower (513 : Fin 1536) ≤ ((136363654140769 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_514 : sigmaFactor (514 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-1873819233 / 46120960 : ℚ) : ℝ) - Real.exp ((-937915979 / 23060480 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_514 : sigmaPower (514 : Fin 1536) ≤ ((136254553557509 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_515 : sigmaFactor (515 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-936024353 / 23056384 : ℚ) : ℝ) - Real.exp ((-3748122147 / 92225536 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_515 : sigmaPower (515 : Fin 1536) ≤ ((2127272097039 / 4398046511104 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_516 : sigmaFactor (516 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-311713149 / 7684096 : ℚ) : ℝ) - Real.exp ((-78012121 / 1921024 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_516 : sigmaPower (516 : Fin 1536) ≤ ((136036236079067 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_517 : sigmaFactor (517 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-109912341 / 2711552 : ℚ) : ℝ) - Real.exp ((-220061347 / 5423104 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_517 : sigmaPower (517 : Fin 1536) ≤ ((135927019142543 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_518 : sigmaFactor (518 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-1866741415 / 46088192 : ℚ) : ℝ) - Real.exp ((-934376355 / 23044096 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_518 : sigmaPower (518 : Fin 1536) ≤ ((67908881690117 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_519 : sigmaFactor (519 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-155414479 / 3840000 : ℚ) : ℝ) - Real.exp ((-1244656457 / 30720000 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_519 : sigmaPower (519 : Fin 1536) ≤ ((135708468771431 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_520 : sigmaFactor (520 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-465801699 / 11517952 : ℚ) : ℝ) - Real.exp ((-58288043 / 1439744 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_520 : sigmaPower (520 : Fin 1536) ≤ ((67799567647707 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_521 : sigmaFactor (521 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-1861440559 / 46063616 : ℚ) : ℝ) - Real.exp ((-3726901563 / 92127232 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_521 : sigmaPower (521 : Fin 1536) ≤ ((33872440732861 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_522 : sigmaFactor (522 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-619891679 / 15351808 : ℚ) : ℝ) - Real.exp ((-310280817 / 7675904 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_522 : sigmaPower (522 : Fin 1536) ≤ ((33845087914693 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_523 : sigmaFactor (523 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-84450465 / 2093056 : ℚ) : ℝ) - Real.exp ((-338167225 / 8372224 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_523 : sigmaPower (523 : Fin 1536) ≤ ((135270901456631 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_524 : sigmaFactor (524 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-928073069 / 23019520 : ℚ) : ℝ) - Real.exp ((-232269411 / 5754880 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_524 : sigmaPower (524 : Fin 1536) ≤ ((8447588269015 / 17592186044416 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_525 : sigmaFactor (525 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-618127587 / 15343616 : ℚ) : ℝ) - Real.exp ((-1237594369 / 30687232 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_525 : sigmaPower (525 : Fin 1536) ≤ ((135051884180803 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_526 : sigmaFactor (526 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-1852620099 / 46022656 : ℚ) : ℝ) - Real.exp ((-927314267 / 23011328 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_526 : sigmaPower (526 : Fin 1536) ≤ ((67471158532755 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_527 : sigmaFactor (527 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-231357269 / 5751808 : ℚ) : ℝ) - Real.exp ((-3705732459 / 92028928 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_527 : sigmaPower (527 : Fin 1536) ≤ ((2106761108399 / 4398046511104 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_528 : sigmaFactor (528 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-77045705 / 1916928 : ℚ) : ℝ) - Real.exp ((-4820585 / 119808 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_528 : sigmaPower (528 : Fin 1536) ≤ ((134723065776041 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_529 : sigmaFactor (529 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-1847336403 / 45998080 : ℚ) : ℝ) - Real.exp ((-3698687531 / 91996160 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_529 : sigmaPower (529 : Fin 1536) ≤ ((134613381560169 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_530 : sigmaFactor (530 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-1845576601 / 45989888 : ℚ) : ℝ) - Real.exp ((-923791803 / 22994944 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_530 : sigmaPower (530 : Fin 1536) ≤ ((33625914567263 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_531 : sigmaFactor (531 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-307302919 / 7663616 : ℚ) : ℝ) - Real.exp ((-1230549441 / 30654464 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_531 : sigmaPower (531 : Fin 1536) ≤ ((134393895881803 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_532 : sigmaFactor (532 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-921029571 / 22986752 : ℚ) : ℝ) - Real.exp ((-230508179 / 5746688 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_532 : sigmaPower (532 : Fin 1536) ≤ ((33571023594381 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_533 : sigmaFactor (533 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-1840301485 / 45965312 : ℚ) : ℝ) - Real.exp ((-3684614835 / 91930624 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_533 : sigmaPower (533 : Fin 1536) ≤ ((33543563433825 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_534 : sigmaFactor (534 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-3277263 / 81920 : ℚ) : ℝ) - Real.exp ((-1640419 / 40960 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_534 : sigmaPower (534 : Fin 1536) ≤ ((67032186967101 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_535 : sigmaFactor (535 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-459197079 / 11487232 : ℚ) : ℝ) - Real.exp ((-3677587067 / 91897856 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_535 : sigmaPower (535 : Fin 1536) ≤ ((66977227476643 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_536 : sigmaFactor (536 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-458758201 / 11485184 : ℚ) : ℝ) - Real.exp ((-57407427 / 1435648 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_536 : sigmaPower (536 : Fin 1536) ≤ ((16730562096449 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_537 : sigmaFactor (537 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-611092669 / 15310848 : ℚ) : ℝ) - Real.exp ((-1223521673 / 30621696 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_537 : sigmaPower (537 : Fin 1536) ≤ ((133734499368145 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_538 : sigmaFactor (538 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-1831523925 / 45924352 : ℚ) : ℝ) - Real.exp ((-916764035 / 22962176 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_538 : sigmaPower (538 : Fin 1536) ≤ ((66812231360979 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_539 : sigmaFactor (539 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-914885279 / 22958080 : ℚ) : ℝ) - Real.exp ((-3663548691 / 91832320 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_539 : sigmaPower (539 : Fin 1536) ≤ ((133514386812025 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_540 : sigmaFactor (540 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-304669651 / 7651328 : ℚ) : ℝ) - Real.exp ((-76250889 / 1912832 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_540 : sigmaPower (540 : Fin 1536) ≤ ((8337766976083 / 17592186044416 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_541 : sigmaFactor (541 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-1826265969 / 45899776 : ℚ) : ℝ) - Real.exp ((-3656538083 / 91799552 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_541 : sigmaPower (541 : Fin 1536) ≤ ((4165441159901 / 8796093022208 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_542 : sigmaFactor (542 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-1824514747 / 45891584 : ℚ) : ℝ) - Real.exp ((-913258731 / 22945792 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_542 : sigmaPower (542 : Fin 1536) ≤ ((133183923289489 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_543 : sigmaFactor (543 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-37974255 / 955904 : ℚ) : ℝ) - Real.exp ((-1216511065 / 30588928 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_543 : sigmaPower (543 : Fin 1536) ≤ ((133073690114233 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_544 : sigmaFactor (544 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-113813403 / 2867200 : ℚ) : ℝ) - Real.exp ((-3560579 / 89600 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_544 : sigmaPower (544 : Fin 1536) ≤ ((132963417569987 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_545 : sigmaFactor (545 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-165387761 / 4169728 : ℚ) : ℝ) - Real.exp ((-331139457 / 8339456 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_545 : sigmaPower (545 : Fin 1536) ≤ ((132853105635655 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_546 : sigmaFactor (546 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-605839003 / 15286272 : ℚ) : ℝ) - Real.exp ((-303253049 / 7643136 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_546 : sigmaPower (546 : Fin 1536) ≤ ((8296422143133 / 17592186044416 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_547 : sigmaFactor (547 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-907884681 / 22925312 : ℚ) : ℝ) - Real.exp ((-3635540579 / 91701248 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_547 : sigmaPower (547 : Fin 1536) ≤ ((66316181756141 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_548 : sigmaFactor (548 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-907011215 / 22921216 : ℚ) : ℝ) - Real.exp ((-227002875 / 5730304 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_548 : sigmaPower (548 : Fin 1536) ≤ ((8282620830061 / 17592186044416 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_549 : sigmaFactor (549 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-604092071 / 15278080 : ℚ) : ℝ) - Real.exp ((-1209517617 / 30556160 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_549 : sigmaPower (549 : Fin 1536) ≤ ((66205731787529 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_550 : sigmaFactor (550 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-1810530711 / 45826048 : ℚ) : ℝ) - Real.exp ((-906265283 / 22913024 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_550 : sigmaPower (550 : Fin 1536) ≤ ((33075238593339 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_551 : sigmaFactor (551 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-26599793 / 673792 : ℚ) : ℝ) - Real.exp ((-213033579 / 5390336 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_551 : sigmaPower (551 : Fin 1536) ≤ ((66095202827343 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_552 : sigmaFactor (552 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-150586821 / 3817472 : ℚ) : ℝ) - Real.exp ((-18844177 / 477184 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_552 : sigmaPower (552 : Fin 1536) ≤ ((16509977174731 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_553 : sigmaFactor (553 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-1805298495 / 45801472 : ℚ) : ℝ) - Real.exp ((-3614594555 / 91602944 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_553 : sigmaPower (553 : Fin 1536) ≤ ((65984594790813 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_554 : sigmaFactor (554 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-1803555853 / 45793280 : ℚ) : ℝ) - Real.exp ((-902777139 / 22896640 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_554 : sigmaPower (554 : Fin 1536) ≤ ((65929261092395 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_555 : sigmaFactor (555 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-300302321 / 7630848 : ℚ) : ℝ) - Real.exp ((-1202541329 / 30523392 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_555 : sigmaPower (555 : Fin 1536) ≤ ((65873907593047 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_556 : sigmaFactor (556 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-81821487 / 2080768 : ℚ) : ℝ) - Real.exp ((-20478073 / 520192 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_556 : sigmaPower (556 : Fin 1536) ≤ ((65818534282139 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_557 : sigmaFactor (557 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-1798332217 / 45768704 : ℚ) : ℝ) - Real.exp ((-3600659139 / 91537408 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_557 : sigmaPower (557 : Fin 1536) ≤ ((131526282298065 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_558 : sigmaFactor (558 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-598864145 / 15253504 : ℚ) : ℝ) - Real.exp ((-299764905 / 7626752 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_558 : sigmaPower (558 : Fin 1536) ≤ ((32853864091541 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_559 : sigmaFactor (559 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-224356671 / 5719040 : ℚ) : ℝ) - Real.exp ((-3593700011 / 91504640 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_559 : sigmaPower (559 : Fin 1536) ≤ ((131304590747269 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_560 : sigmaFactor (560 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-224139377 / 5718016 : ℚ) : ℝ) - Real.exp ((-14024307 / 357376 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_560 : sigmaPower (560 : Fin 1536) ≤ ((65596842710029 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_561 : sigmaFactor (561 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-597125793 / 15245312 : ℚ) : ℝ) - Real.exp ((-1195582201 / 30490624 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_561 : sigmaPower (561 : Fin 1536) ≤ ((131082740363193 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_562 : sigmaFactor (562 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-1789640457 / 45727744 : ℚ) : ℝ) - Real.exp ((-895818011 / 22863872 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_562 : sigmaPower (562 : Fin 1536) ≤ ((130971755555323 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_563 : sigmaFactor (563 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-893952125 / 22859776 : ℚ) : ℝ) - Real.exp ((-3579798915 / 91439104 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_563 : sigmaPower (563 : Fin 1536) ≤ ((130860730975079 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_564 : sigmaFactor (564 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-297694793 / 7618560 : ℚ) : ℝ) - Real.exp ((-74506817 / 1904640 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_564 : sigmaPower (564 : Fin 1536) ≤ ((130749666601079 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_565 : sigmaFactor (565 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-1784433981 / 45703168 : ℚ) : ℝ) - Real.exp ((-3572856947 / 91406336 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_565 : sigmaPower (565 : Fin 1536) ≤ ((130638562411925 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_566 : sigmaFactor (566 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-1782699919 / 45694976 : ℚ) : ℝ) - Real.exp ((-892347027 / 22847488 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_566 : sigmaPower (566 : Fin 1536) ≤ ((65263709193101 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_567 : sigmaFactor (567 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-13492171 / 346112 : ℚ) : ℝ) - Real.exp ((-108058203 / 2768896 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_567 : sigmaPower (567 : Fin 1536) ≤ ((130416234502481 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_568 : sigmaFactor (568 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-26165205 / 671744 : ℚ) : ℝ) - Real.exp ((-3274315 / 83968 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_568 : sigmaPower (568 : Fin 1536) ≤ ((130305010739319 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_569 : sigmaFactor (569 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-1777502023 / 45670400 : ℚ) : ℝ) - Real.exp ((-3558990171 / 91340800 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_569 : sigmaPower (569 : Fin 1536) ≤ ((130193747075255 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_570 : sigmaFactor (570 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-591923607 / 15220736 : ℚ) : ℝ) - Real.exp ((-296293921 / 7610368 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_570 : sigmaPower (570 : Fin 1536) ≤ ((130082443488815 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_571 : sigmaFactor (571 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-887020167 / 22827008 : ℚ) : ℝ) - Real.exp ((-3552065363 / 91308032 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_571 : sigmaPower (571 : Fin 1536) ≤ ((129971099958507 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_572 : sigmaFactor (572 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-886155281 / 22822912 : ℚ) : ℝ) - Real.exp ((-221787819 / 5705728 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_572 : sigmaPower (572 : Fin 1536) ≤ ((129859716462825 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_573 : sigmaFactor (573 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-590193835 / 15212544 : ℚ) : ℝ) - Real.exp ((-1181715425 / 30425088 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_573 : sigmaPower (573 : Fin 1536) ≤ ((129748292980249 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_574 : sigmaFactor (574 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-1768853163 / 45629440 : ℚ) : ℝ) - Real.exp ((-885422219 / 22814720 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_574 : sigmaPower (574 : Fin 1536) ≤ ((129636829489241 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_575 : sigmaFactor (575 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-55222673 / 1425664 : ℚ) : ℝ) - Real.exp ((-3538232907 / 91242496 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_575 : sigmaPower (575 : Fin 1536) ≤ ((129525325968249 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_576 : sigmaFactor (576 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-18389569 / 475136 : ℚ) : ℝ) - Real.exp ((-287661 / 7424 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_576 : sigmaPower (576 : Fin 1536) ≤ ((16176722799463 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_577 : sigmaFactor (577 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-1763672427 / 45604864 : ℚ) : ℝ) - Real.exp ((-3531325259 / 91209728 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_577 : sigmaPower (577 : Fin 1536) ≤ ((129302198750025 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_578 : sigmaFactor (578 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-14561545 / 376832 : ℚ) : ℝ) - Real.exp ((-7288995 / 188416 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_578 : sigmaPower (578 : Fin 1536) ≤ ((64595287504805 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_579 : sigmaFactor (579 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-293370363 / 7598080 : ℚ) : ℝ) - Real.exp ((-1174807777 / 30392320 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_579 : sigmaPower (579 : Fin 1536) ≤ ((8067431947053 / 17592186044416 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_580 : sigmaFactor (580 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-879249063 / 22790144 : ℚ) : ℝ) - Real.exp ((-220060907 / 5697536 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_580 : sigmaPower (580 : Fin 1536) ≤ ((64483603579053 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_581 : sigmaFactor (581 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-1756774789 / 45572096 : ℚ) : ℝ) - Real.exp ((-3517527123 / 91144192 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_581 : sigmaPower (581 : Fin 1536) ≤ ((32213865750935 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_582 : sigmaFactor (582 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-585017389 / 15187968 : ℚ) : ℝ) - Real.exp ((-292840097 / 7593984 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_582 : sigmaPower (582 : Fin 1536) ≤ ((128743678668089 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_583 : sigmaFactor (583 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-438332565 / 11388928 : ℚ) : ℝ) - Real.exp ((-3510636635 / 91111424 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_583 : sigmaPower (583 : Fin 1536) ≤ ((32157963532369 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_584 : sigmaFactor (584 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-437902267 / 11386880 : ℚ) : ℝ) - Real.exp ((-54799899 / 1423360 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_584 : sigmaPower (584 : Fin 1536) ≤ ((128519989366209 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_585 : sigmaFactor (585 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-34311541 / 892928 : ℚ) : ℝ) - Real.exp ((-68701017 / 1785856 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_585 : sigmaPower (585 : Fin 1536) ≤ ((32102021089145 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_586 : sigmaFactor (586 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-1748168829 / 45531136 : ℚ) : ℝ) - Real.exp ((-875077907 / 22765568 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_586 : sigmaPower (586 : Fin 1536) ≤ ((128296139078865 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_587 : sigmaFactor (587 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-873224891 / 22761472 : ℚ) : ℝ) - Real.exp ((-3496872819 / 91045888 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_587 : sigmaPower (587 : Fin 1536) ≤ ((64092076755663 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_588 : sigmaFactor (588 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-290788575 / 7585792 : ℚ) : ℝ) - Real.exp ((-72779905 / 1896448 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_588 : sigmaPower (588 : Fin 1536) ≤ ((128072127632207 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_589 : sigmaFactor (589 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-158455803 / 4136960 : ℚ) : ℝ) - Real.exp ((-317272681 / 8273920 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_589 : sigmaPower (589 : Fin 1536) ≤ ((63980030709869 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_590 : sigmaFactor (590 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-1741296931 / 45498368 : ℚ) : ℝ) - Real.exp ((-871641243 / 22749184 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_590 : sigmaPower (590 : Fin 1536) ≤ ((63923977426067 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_591 : sigmaFactor (591 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-72482531 / 1895424 : ℚ) : ℝ) - Real.exp ((-1161043961 / 30326784 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_591 : sigmaPower (591 : Fin 1536) ≤ ((15966975988449 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_592 : sigmaFactor (592 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-217233159 / 5685248 : ℚ) : ℝ) - Real.exp ((-13592579 / 355328 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_592 : sigmaPower (592 : Fin 1536) ≤ ((63811810282147 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_593 : sigmaFactor (593 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-1736150515 / 45473792 : ℚ) : ℝ) - Real.exp ((-3476269995 / 90947584 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_593 : sigmaPower (593 : Fin 1536) ≤ ((15938924100051 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_594 : sigmaFactor (594 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-578145491 / 15155200 : ℚ) : ℝ) - Real.exp ((-289403433 / 7577600 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_594 : sigmaPower (594 : Fin 1536) ≤ ((127399124594085 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_595 : sigmaFactor (595 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-866361573 / 22728704 : ℚ) : ℝ) - Real.exp ((-3469413827 / 90914816 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_595 : sigmaPower (595 : Fin 1536) ≤ ((127286815923459 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_596 : sigmaFactor (596 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-865505267 / 22724608 : ℚ) : ℝ) - Real.exp ((-216624243 / 5681152 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_596 : sigmaPower (596 : Fin 1536) ≤ ((127174466766651 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_597 : sigmaFactor (597 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-576432879 / 15147008 : ℚ) : ℝ) - Real.exp ((-1154187793 / 30294016 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_597 : sigmaPower (597 : Fin 1536) ≤ ((31765519275441 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_598 : sigmaFactor (598 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-1727587455 / 45432832 : ℚ) : ℝ) - Real.exp ((-864785075 / 22716416 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_598 : sigmaPower (598 : Fin 1536) ≤ ((63474823453443 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_599 : sigmaFactor (599 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-431469247 / 11356160 : ℚ) : ℝ) - Real.exp ((-3455718651 / 90849280 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_599 : sigmaPower (599 : Fin 1536) ≤ ((126837176160089 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_600 : sigmaFactor (600 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-13061873 / 344064 : ℚ) : ℝ) - Real.exp ((-1634611 / 43008 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_600 : sigmaPower (600 : Fin 1536) ≤ ((63362332419715 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_601 : sigmaFactor (601 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-1722458199 / 45408256 : ℚ) : ℝ) - Real.exp ((-3448879643 / 90816512 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_601 : sigmaPower (601 : Fin 1536) ≤ ((126612112922949 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_602 : sigmaFactor (602 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-101220581 / 2670592 : ℚ) : ℝ) - Real.exp ((-50668563 / 1335296 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_602 : sigmaPower (602 : Fin 1536) ≤ ((63249760194335 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_603 : sigmaFactor (603 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-286507045 / 7565312 : ℚ) : ℝ) - Real.exp ((-1147348785 / 30261248 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_603 : sigmaPower (603 : Fin 1536) ≤ ((126386887214603 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_604 : sigmaFactor (604 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-858667689 / 22691840 : ℚ) : ℝ) - Real.exp ((-214914491 / 5672960 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_604 : sigmaPower (604 : Fin 1536) ≤ ((31568553344685 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_605 : sigmaFactor (605 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-1715629201 / 45375488 : ℚ) : ℝ) - Real.exp ((-3435218787 / 90750976 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_605 : sigmaPower (605 : Fin 1536) ≤ ((63080749429529 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_606 : sigmaFactor (606 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-571307913 / 15122432 : ℚ) : ℝ) - Real.exp ((-285983929 / 7561216 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_606 : sigmaPower (606 : Fin 1536) ≤ ((126048743633519 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_607 : sigmaFactor (607 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-107013687 / 2834944 : ℚ) : ℝ) - Real.exp ((-3428396939 / 90718208 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_607 : sigmaPower (607 : Fin 1536) ≤ ((31483986920017 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_608 : sigmaFactor (608 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-106907185 / 2834432 : ℚ) : ℝ) - Real.exp ((-3344715 / 88576 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_608 : sigmaPower (608 : Fin 1536) ≤ ((125823110976633 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_609 : sigmaFactor (609 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-569603881 / 15114240 : ℚ) : ℝ) - Real.exp ((-1140526937 / 30228480 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_609 : sigmaPower (609 : Fin 1536) ≤ ((15713779187641 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_610 : sigmaFactor (610 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-1707109041 / 45334528 : ℚ) : ℝ) - Real.exp ((-854543723 / 22667264 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_610 : sigmaPower (610 : Fin 1536) ≤ ((125597315231451 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_611 : sigmaFactor (611 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-77518507 / 2060288 : ℚ) : ℝ) - Real.exp ((-310433673 / 8241152 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_611 : sigmaPower (611 : Fin 1536) ≤ ((62742178072741 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_612 : sigmaFactor (612 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-283950997 / 7553024 : ℚ) : ℝ) - Real.exp ((-71070153 / 1888256 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_612 : sigmaPower (612 : Fin 1536) ≤ ((3917854881909 / 8796093022208 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_613 : sigmaFactor (613 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-1702005525 / 45309952 : ℚ) : ℝ) - Real.exp ((-3407965715 / 90619904 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_613 : sigmaPower (613 : Fin 1536) ≤ ((125258315436117 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_614 : sigmaFactor (614 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-1700305783 / 45301760 : ℚ) : ℝ) - Real.exp ((-851141379 / 22650880 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_614 : sigmaPower (614 : Fin 1536) ≤ ((125145233768403 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_615 : sigmaFactor (615 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-141550563 / 3774464 : ℚ) : ℝ) - Real.exp ((-1133722249 / 30195712 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_615 : sigmaPower (615 : Fin 1536) ≤ ((125032111195763 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_616 : sigmaFactor (616 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-424227111 / 11321344 : ℚ) : ℝ) - Real.exp ((-53090147 / 1415168 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_616 : sigmaPower (616 : Fin 1536) ≤ ((62459473847999 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_617 : sigmaFactor (617 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-1695210847 / 45277184 : ℚ) : ℝ) - Real.exp ((-3394373499 / 90554368 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_617 : sigmaPower (617 : Fin 1536) ≤ ((62402871623447 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_618 : sigmaFactor (618 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-564504655 / 15089664 : ℚ) : ℝ) - Real.exp ((-282581585 / 7544832 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_618 : sigmaPower (618 : Fin 1536) ≤ ((124692497826219 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_619 : sigmaFactor (619 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-49759347 / 1331200 : ℚ) : ℝ) - Real.exp ((-199269763 / 5324800 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_619 : sigmaPower (619 : Fin 1536) ≤ ((124579211411727 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_620 : sigmaFactor (620 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-845061173 / 22626304 : ℚ) : ℝ) - Real.exp ((-211512147 / 5656576 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_620 : sigmaPower (620 : Fin 1536) ≤ ((124465883981155 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_621 : sigmaFactor (621 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-562809203 / 15081472 : ℚ) : ℝ) - Real.exp ((-1126934721 / 30162944 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_621 : sigmaPower (621 : Fin 1536) ≤ ((62176257756111 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_622 : sigmaFactor (622 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-153339417 / 4112384 : ℚ) : ℝ) - Real.exp ((-76759441 / 2056192 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_622 : sigmaPower (622 : Fin 1536) ≤ ((124239105982635 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_623 : sigmaFactor (623 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-210630035 / 5653504 : ℚ) : ℝ) - Real.exp ((-3374028075 / 90456064 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_623 : sigmaPower (623 : Fin 1536) ≤ ((3878926730315 / 8796093022208 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_624 : sigmaFactor (624 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-70139487 / 1884160 : ℚ) : ℝ) - Real.exp ((-4388857 / 117760 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_624 : sigmaPower (624 : Fin 1536) ≤ ((15501520456529 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_625 : sigmaFactor (625 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-1681655811 / 45211648 : ℚ) : ℝ) - Real.exp ((-3367257707 / 90423296 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_625 : sigmaPower (625 : Fin 1536) ≤ ((123898630806745 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_626 : sigmaFactor (626 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-1679964649 / 45203456 : ℚ) : ℝ) - Real.exp ((-840968667 / 22601728 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_626 : sigmaPower (626 : Fin 1536) ≤ ((123785056811259 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_627 : sigmaFactor (627 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-279712367 / 7532544 : ℚ) : ℝ) - Real.exp ((-1120164353 / 30130176 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_627 : sigmaPower (627 : Fin 1536) ≤ ((123671441643399 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_628 : sigmaFactor (628 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-838292235 / 22593536 : ℚ) : ℝ) - Real.exp ((-209819555 / 5648384 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_628 : sigmaPower (628 : Fin 1536) ≤ ((30889446320193 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_629 : sigmaFactor (629 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-1674895453 / 45178880 : ℚ) : ℝ) - Real.exp ((-3353734131 / 90357760 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_629 : sigmaPower (629 : Fin 1536) ≤ ((123444087700969 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_630 : sigmaFactor (630 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-557735717 / 15056896 : ℚ) : ℝ) - Real.exp ((-279196401 / 7528448 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_630 : sigmaPower (630 : Fin 1536) ≤ ((123330348881565 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_631 : sigmaFactor (631 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-417879891 / 11290624 : ℚ) : ℝ) - Real.exp ((-3346980923 / 90324992 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_631 : sigmaPower (631 : Fin 1536) ≤ ((61608284400059 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_632 : sigmaFactor (632 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-417458173 / 11288576 : ℚ) : ℝ) - Real.exp ((-52243851 / 1411072 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_632 : sigmaPower (632 : Fin 1536) ≤ ((30775686858543 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_633 : sigmaFactor (633 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-50549895 / 1368064 : ℚ) : ℝ) - Real.exp ((-101219195 / 2736128 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_633 : sigmaPower (633 : Fin 1536) ≤ ((30747221190313 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_634 : sigmaFactor (634 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-1666461093 / 45137920 : ℚ) : ℝ) - Real.exp ((-834215459 / 22568960 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_634 : sigmaPower (634 : Fin 1536) ≤ ((122874980758869 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_635 : sigmaFactor (635 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-832388183 / 22564864 : ℚ) : ℝ) - Real.exp ((-3333491667 / 90259456 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_635 : sigmaPower (635 : Fin 1536) ≤ ((122761035404515 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_636 : sigmaFactor (636 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-16304827 / 442368 : ℚ) : ℝ) - Real.exp ((-4081033 / 110592 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_636 : sigmaPower (636 : Fin 1536) ≤ ((30661762168917 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_637 : sigmaFactor (637 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-1661409057 / 45113344 : ℚ) : ℝ) - Real.exp ((-3326755619 / 90226688 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_637 : sigmaPower (637 : Fin 1536) ≤ ((30633255137447 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_638 : sigmaFactor (638 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-1659726475 / 45105152 : ℚ) : ℝ) - Real.exp ((-830847435 / 22552576 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_638 : sigmaPower (638 : Fin 1536) ≤ ((3825592218885 / 8796093022208 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_639 : sigmaFactor (639 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-8635649 / 234880 : ℚ) : ℝ) - Real.exp ((-1106675097 / 30064640 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_639 : sigmaPower (639 : Fin 1536) ≤ ((30576210004173 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

end LegendreK6.M2Pilot.Enclosures.Sigma004
