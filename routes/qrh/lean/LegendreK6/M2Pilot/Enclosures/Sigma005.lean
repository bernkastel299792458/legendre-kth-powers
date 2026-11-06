import LegendreK6.M2PilotDefinitions
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp

/-! Generated proposals: every bound is checked by Lean, not by trusting Arb. -/
namespace LegendreK6.M2Pilot.Enclosures.Sigma005
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem sigma_factor_upper_640 : sigmaFactor (640 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-25880679 / 704512 : ℚ) : ℝ) - Real.exp ((-202433 / 5504 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_640 : sigmaPower (640 : Fin 1536) ≤ ((30547671891079 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_641 : sigmaFactor (641 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-1654683019 / 45080576 : ℚ) : ℝ) - Real.exp ((-3313300683 / 90161152 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_641 : sigmaPower (641 : Fin 1536) ≤ ((122076493624587 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_642 : sigmaFactor (642 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-551001099 / 15024128 : ℚ) : ℝ) - Real.exp ((-275828377 / 7512064 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_642 : sigmaPower (642 : Fin 1536) ≤ ((121962258174883 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_643 : sigmaFactor (643 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-825662145 / 22532096 : ℚ) : ℝ) - Real.exp ((-3306581795 / 90128384 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_643 : sigmaPower (643 : Fin 1536) ≤ ((121847981192567 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_644 : sigmaFactor (644 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-74983909 / 2048000 : ℚ) : ℝ) - Real.exp ((-18768321 / 512000 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_644 : sigmaPower (644 : Fin 1536) ≤ ((121733662654985 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_645 : sigmaFactor (645 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-549322807 / 15015936 : ℚ) : ℝ) - Real.exp ((-1099956209 / 30031872 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_645 : sigmaPower (645 : Fin 1536) ≤ ((60809651269733 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_646 : sigmaFactor (646 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-1646291559 / 45039616 : ℚ) : ℝ) - Real.exp ((-824128547 / 22519808 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_646 : sigmaPower (646 : Fin 1536) ≤ ((60752450411661 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_647 : sigmaFactor (647 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-411153853 / 11257856 : ℚ) : ℝ) - Real.exp ((-3293161179 / 90062848 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_647 : sigmaPower (647 : Fin 1536) ≤ ((121390457483851 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_648 : sigmaFactor (648 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-136911665 / 3751936 : ℚ) : ℝ) - Real.exp ((-17134425 / 468992 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_648 : sigmaPower (648 : Fin 1536) ≤ ((121275972498333 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_649 : sigmaFactor (649 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-1641265263 / 45015040 : ℚ) : ℝ) - Real.exp ((-3286459451 / 90030080 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_649 : sigmaPower (649 : Fin 1536) ≤ ((121161445844029 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_650 : sigmaFactor (650 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-1639591261 / 45006848 : ℚ) : ℝ) - Real.exp ((-820777683 / 22503424 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_650 : sigmaPower (650 : Fin 1536) ≤ ((30261719374547 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_651 : sigmaFactor (651 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-272986329 / 7499776 : ℚ) : ℝ) - Real.exp ((-1093254481 / 29999104 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_651 : sigmaPower (651 : Fin 1536) ≤ ((120932267438039 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_652 : sigmaFactor (652 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-818122701 / 22495232 : ℚ) : ℝ) - Real.exp ((-204776099 / 5623808 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_652 : sigmaPower (652 : Fin 1536) ≤ ((120817615640797 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_653 : sigmaFactor (653 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-96151385 / 2646016 : ℚ) : ℝ) - Real.exp ((-192533715 / 5292032 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_653 : sigmaPower (653 : Fin 1536) ≤ ((120702922083657 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_654 : sigmaFactor (654 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-544300801 / 14991360 : ℚ) : ℝ) - Real.exp ((-272477513 / 7495680 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_654 : sigmaPower (654 : Fin 1536) ≤ ((120588186743801 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_655 : sigmaFactor (655 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-18536727 / 510976 : ℚ) : ℝ) - Real.exp ((-296944417 / 8175616 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_655 : sigmaPower (655 : Fin 1536) ≤ ((120473409598391 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_656 : sigmaFactor (656 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-203695283 / 5619712 : ℚ) : ℝ) - Real.exp ((-12746283 / 351232 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_656 : sigmaPower (656 : Fin 1536) ≤ ((1880602978509 / 4398046511104 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_657 : sigmaFactor (657 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-542631089 / 14983168 : ℚ) : ℝ) - Real.exp ((-1086569913 / 29966336 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_657 : sigmaPower (657 : Fin 1536) ≤ ((60121864899743 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_658 : sigmaFactor (658 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-1626224985 / 44941312 : ℚ) : ℝ) - Real.exp ((-814093115 / 22470656 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_658 : sigmaPower (658 : Fin 1536) ≤ ((60064413550117 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_659 : sigmaFactor (659 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-812278709 / 22466560 : ℚ) : ℝ) - Real.exp ((-3253036611 / 89866240 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_659 : sigmaPower (659 : Fin 1536) ≤ ((60006941251959 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_660 : sigmaFactor (660 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-270481761 / 7487488 : ℚ) : ℝ) - Real.exp ((-67702129 / 1871872 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_660 : sigmaPower (660 : Fin 1536) ≤ ((59949447993809 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_661 : sigmaFactor (661 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-1621224429 / 44916736 : ℚ) : ℝ) - Real.exp ((-3246369203 / 89833472 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_661 : sigmaPower (661 : Fin 1536) ≤ ((119783867528397 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_662 : sigmaFactor (662 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-1619559007 / 44908544 : ℚ) : ℝ) - Real.exp ((-810759411 / 22454272 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_662 : sigmaPower (662 : Fin 1536) ≤ ((119668797103303 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_663 : sigmaFactor (663 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-134824525 / 3741696 : ℚ) : ℝ) - Real.exp ((-1079902505 / 29933568 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_663 : sigmaPower (663 : Fin 1536) ≤ ((119553684689365 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_664 : sigmaFactor (664 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-404057577 / 11223040 : ℚ) : ℝ) - Real.exp ((-50568419 / 1402880 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_664 : sigmaPower (664 : Fin 1536) ≤ ((59719265131799 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_665 : sigmaFactor (665 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-1614567031 / 44883968 : ℚ) : ℝ) - Real.exp ((-3233051547 / 89767936 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_665 : sigmaPower (665 : Fin 1536) ≤ ((119323333802997 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_666 : sigmaFactor (666 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-48875893 / 1359872 : ℚ) : ℝ) - Real.exp ((-24467619 / 679936 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_666 : sigmaPower (666 : Fin 1536) ≤ ((119208095284543 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_667 : sigmaFactor (667 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-805621311 / 22433792 : ℚ) : ℝ) - Real.exp ((-3226401299 / 89735168 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_667 : sigmaPower (667 : Fin 1536) ≤ ((59546407342599 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_668 : sigmaFactor (668 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-804790745 / 22429696 : ℚ) : ℝ) - Real.exp ((-201442395 / 5607424 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_668 : sigmaPower (668 : Fin 1536) ≤ ((118977491981909 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_669 : sigmaFactor (669 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-535973691 / 14950400 : ℚ) : ℝ) - Real.exp ((-1073252257 / 29900800 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_669 : sigmaPower (669 : Fin 1536) ≤ ((118862127151605 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_670 : sigmaFactor (670 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-94485963 / 2637824 : ℚ) : ℝ) - Real.exp ((-47300539 / 1318912 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_670 : sigmaPower (670 : Fin 1536) ≤ ((118746720171199 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_671 : sigmaFactor (671 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-100287649 / 2802176 : ℚ) : ℝ) - Real.exp ((-3213117963 / 89669632 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_671 : sigmaPower (671 : Fin 1536) ≤ ((59315635508793 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_672 : sigmaFactor (672 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-33394669 / 933888 : ℚ) : ℝ) - Real.exp ((-1044857 / 29184 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_672 : sigmaPower (672 : Fin 1536) ≤ ((118515779667645 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_673 : sigmaFactor (673 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-1601286555 / 44818432 : ℚ) : ℝ) - Real.exp ((-3206484875 / 89636864 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_673 : sigmaPower (673 : Fin 1536) ≤ ((59200123049119 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_674 : sigmaFactor (674 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-1599629713 / 44810240 : ℚ) : ℝ) - Real.exp ((-800792619 / 22405120 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_674 : sigmaPower (674 : Fin 1536) ≤ ((118284670286209 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_675 : sigmaFactor (675 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-266328931 / 7467008 : ℚ) : ℝ) - Real.exp ((-1066619169 / 29868032 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_675 : sigmaPower (675 : Fin 1536) ≤ ((118169052208387 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_676 : sigmaFactor (676 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-798159087 / 22396928 : ℚ) : ℝ) - Real.exp ((-199784123 / 5599232 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_676 : sigmaPower (676 : Fin 1536) ≤ ((118053391841583 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_677 : sigmaFactor (677 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-144969407 / 4071424 : ℚ) : ℝ) - Real.exp ((-290294169 / 8142848 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_677 : sigmaPower (677 : Fin 1536) ≤ ((58968844581295 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_678 : sigmaFactor (678 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-531003165 / 14925824 : ℚ) : ℝ) - Real.exp ((-265827265 / 7462912 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_678 : sigmaPower (678 : Fin 1536) ≤ ((58910972074093 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_679 : sigmaFactor (679 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-397839057 / 11192320 : ℚ) : ℝ) - Real.exp ((-3186619931 / 89538560 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_679 : sigmaPower (679 : Fin 1536) ≤ ((117706156775131 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_680 : sigmaFactor (680 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-397425919 / 11190272 : ℚ) : ℝ) - Real.exp ((-49739283 / 1398784 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_680 : sigmaPower (680 : Fin 1536) ≤ ((117590327020167 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_681 : sigmaFactor (681 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-529350613 / 14917632 : ℚ) : ℝ) - Real.exp ((-1060003241 / 29835264 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_681 : sigmaPower (681 : Fin 1536) ≤ ((58737227430011 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_682 : sigmaFactor (682 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-1586400717 / 44744704 : ℚ) : ℝ) - Real.exp ((-794176691 / 22372352 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_682 : sigmaPower (682 : Fin 1536) ≤ ((117358540271403 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_683 : sigmaFactor (683 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-792375155 / 22368256 : ℚ) : ℝ) - Real.exp ((-3173405235 / 89473024 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_683 : sigmaPower (683 : Fin 1536) ≤ ((117242583231003 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_684 : sigmaFactor (684 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-263850103 / 7454720 : ℚ) : ℝ) - Real.exp ((-66043857 / 1863680 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_684 : sigmaPower (684 : Fin 1536) ≤ ((117126583715497 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_685 : sigmaFactor (685 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-1581451641 / 44720128 : ℚ) : ℝ) - Real.exp ((-3166806467 / 89440256 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_685 : sigmaPower (685 : Fin 1536) ≤ ((58505270850771 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_686 : sigmaFactor (686 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-1579803379 / 44711936 : ℚ) : ℝ) - Real.exp ((-790877307 / 22355968 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_686 : sigmaPower (686 : Fin 1536) ≤ ((116894457165779 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_687 : sigmaFactor (687 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-3868029 / 109568 : ℚ) : ℝ) - Real.exp ((-61964969 / 1753088 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_687 : sigmaPower (687 : Fin 1536) ≤ ((3649322815151 / 8796093022208 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_688 : sigmaFactor (688 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-17914875 / 507904 : ℚ) : ℝ) - Real.exp ((-1121065 / 31744 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_688 : sigmaPower (688 : Fin 1536) ≤ ((116662160435307 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_689 : sigmaFactor (689 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-1574862883 / 44687360 : ℚ) : ℝ) - Real.exp ((-3153626091 / 89374720 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_689 : sigmaPower (689 : Fin 1536) ≤ ((113814402533 / 274877906944 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_690 : sigmaFactor (690 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-524405827 / 14893056 : ℚ) : ℝ) - Real.exp ((-262527881 / 7446528 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_690 : sigmaPower (690 : Fin 1536) ≤ ((58214846668431 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_691 : sigmaFactor (691 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-785786397 / 22335488 : ℚ) : ℝ) - Real.exp ((-3147044483 / 89341952 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_691 : sigmaPower (691 : Fin 1536) ≤ ((116313395841069 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_692 : sigmaFactor (692 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-784964411 / 22331392 : ℚ) : ℝ) - Real.exp ((-196484739 / 5582848 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_692 : sigmaPower (692 : Fin 1536) ≤ ((14524631960369 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_693 : sigmaFactor (693 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-522761855 / 14884864 : ℚ) : ℝ) - Real.exp ((-1046822865 / 29769728 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_693 : sigmaPower (693 : Fin 1536) ≤ ((116080672839031 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_694 : sigmaFactor (694 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-1566643023 / 44646400 : ℚ) : ℝ) - Real.exp ((-784295699 / 22323200 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_694 : sigmaPower (694 : Fin 1536) ≤ ((57982123642905 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_695 : sigmaFactor (695 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-391250299 / 11159552 : ℚ) : ℝ) - Real.exp ((-3133898427 / 89276416 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_695 : sigmaPower (695 : Fin 1536) ≤ ((57923889499887 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_696 : sigmaFactor (696 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-130280007 / 3719168 : ℚ) : ℝ) - Real.exp ((-16305289 / 464896 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_696 : sigmaPower (696 : Fin 1536) ≤ ((7233204247337 / 17592186044416 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_697 : sigmaFactor (697 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-1561719687 / 44621824 : ℚ) : ℝ) - Real.exp ((-3127333979 / 89243648 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_697 : sigmaPower (697 : Fin 1536) ≤ ((28903678533779 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_698 : sigmaFactor (698 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-1560080005 / 44613632 : ℚ) : ℝ) - Real.exp ((-781013475 / 22306816 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_698 : sigmaPower (698 : Fin 1536) ≤ ((28874529377345 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_699 : sigmaFactor (699 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-2146613 / 61440 : ℚ) : ℝ) - Real.exp ((-8597177 / 245760 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_699 : sigmaPower (699 : Fin 1536) ≤ ((14422684757075 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_700 : sigmaFactor (700 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-778401393 / 22298624 : ℚ) : ℝ) - Real.exp ((-194843627 / 5574656 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_700 : sigmaPower (700 : Fin 1536) ≤ ((14408099469147 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_701 : sigmaFactor (701 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-1555165249 / 44589056 : ℚ) : ℝ) - Real.exp ((-3114222243 / 89178112 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_701 : sigmaPower (701 : Fin 1536) ≤ ((115148070575491 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_702 : sigmaFactor (702 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-517842809 / 14860288 : ℚ) : ℝ) - Real.exp ((-259245657 / 7430144 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_702 : sigmaPower (702 : Fin 1536) ≤ ((28757825624977 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_703 : sigmaFactor (703 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-48496635 / 1392896 : ℚ) : ℝ) - Real.exp ((-3107674955 / 89145344 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_703 : sigmaPower (703 : Fin 1536) ≤ ((14364311437847 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_704 : sigmaFactor (704 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-2849737 / 81920 : ℚ) : ℝ) - Real.exp ((-44583 / 1280 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_704 : sigmaPower (704 : Fin 1536) ≤ ((114797637560425 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_705 : sigmaFactor (705 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-516207417 / 14852096 : ℚ) : ℝ) - Real.exp ((-1033711129 / 29704192 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_705 : sigmaPower (705 : Fin 1536) ≤ ((57340370324583 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_706 : sigmaFactor (706 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-1546988289 / 44548096 : ℚ) : ℝ) - Real.exp ((-774466187 / 22274048 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_706 : sigmaPower (706 : Fin 1536) ≤ ((7160237546581 / 17592186044416 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_707 : sigmaFactor (707 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-772677521 / 22269952 : ℚ) : ℝ) - Real.exp ((-3094597539 / 89079808 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_707 : sigmaPower (707 : Fin 1536) ≤ ((28611704456273 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_708 : sigmaFactor (708 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-257287085 / 7421952 : ℚ) : ℝ) - Real.exp ((-64402745 / 1855488 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_708 : sigmaPower (708 : Fin 1536) ≤ ((57164895932407 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_709 : sigmaFactor (709 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-1542090693 / 44523520 : ℚ) : ℝ) - Real.exp ((-3088067411 / 89047040 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_709 : sigmaPower (709 : Fin 1536) ≤ ((57106361420353 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_710 : sigmaFactor (710 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-140041781 / 4046848 : ℚ) : ℝ) - Real.exp ((-70109193 / 2023424 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_710 : sigmaPower (710 : Fin 1536) ≤ ((3565487835281 / 8796093022208 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_711 : sigmaFactor (711 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-128235767 / 3708928 : ℚ) : ℝ) - Real.exp ((-1027181001 / 29671424 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_711 : sigmaPower (711 : Fin 1536) ≤ ((14247306938235 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_712 : sigmaFactor (712 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-384299883 / 11124736 : ℚ) : ℝ) - Real.exp ((-48098171 / 1390592 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_712 : sigmaPower (712 : Fin 1536) ≤ ((113861257147561 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_713 : sigmaFactor (713 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-1535570575 / 44490752 : ℚ) : ℝ) - Real.exp ((-3075024315 / 88981504 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_713 : sigmaPower (713 : Fin 1536) ≤ ((113744015630207 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_714 : sigmaFactor (714 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-511314111 / 14827520 : ℚ) : ℝ) - Real.exp ((-255980593 / 7413760 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_714 : sigmaPower (714 : Fin 1536) ≤ ((56813365464987 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_715 : sigmaFactor (715 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-766157403 / 22237184 : ℚ) : ℝ) - Real.exp ((-3068511347 / 88948736 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_715 : sigmaPower (715 : Fin 1536) ≤ ((14188675377875 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_716 : sigmaFactor (716 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-765343997 / 22233088 : ℚ) : ℝ) - Real.exp ((-191578563 / 5558272 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_716 : sigmaPower (716 : Fin 1536) ≤ ((28348007971351 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_717 : sigmaFactor (717 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-509687299 / 14819328 : ℚ) : ℝ) - Real.exp ((-1020668033 / 29638656 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_717 : sigmaPower (717 : Fin 1536) ≤ ((14159327186661 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_718 : sigmaFactor (718 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-1527436515 / 44449792 : ℚ) : ℝ) - Real.exp ((-764688155 / 22224896 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_718 : sigmaPower (718 : Fin 1536) ≤ ((113157159822739 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_719 : sigmaFactor (719 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-190726481 / 5555200 : ℚ) : ℝ) - Real.exp ((-3055502571 / 88883200 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_719 : sigmaPower (719 : Fin 1536) ≤ ((56519829424911 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_720 : sigmaFactor (720 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-63507829 / 1851392 : ℚ) : ℝ) - Real.exp ((-3974289 / 115712 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_720 : sigmaPower (720 : Fin 1536) ≤ ((28230528637647 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_721 : sigmaFactor (721 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-8142057 / 237568 : ℚ) : ℝ) - Real.exp ((-16304849 / 475136 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_721 : sigmaPower (721 : Fin 1536) ≤ ((112804526901069 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_722 : sigmaFactor (722 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-1520942137 / 44417024 : ℚ) : ℝ) - Real.exp ((-761440251 / 22208512 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_722 : sigmaPower (722 : Fin 1536) ≤ ((56343447938639 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_723 : sigmaFactor (723 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-253220055 / 7401472 : ℚ) : ℝ) - Real.exp ((-1014172225 / 29605888 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_723 : sigmaPower (723 : Fin 1536) ≤ ((28142305363803 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_724 : sigmaFactor (724 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-758849619 / 22200320 : ℚ) : ℝ) - Real.exp ((-189954611 / 5550080 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_724 : sigmaPower (724 : Fin 1536) ≤ ((112451503610851 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_725 : sigmaFactor (725 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-1516078861 / 44392448 : ℚ) : ℝ) - Real.exp ((-3036032307 / 88784896 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_725 : sigmaPower (725 : Fin 1536) ≤ ((56166871160077 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_726 : sigmaFactor (726 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-504819733 / 14794752 : ℚ) : ℝ) - Real.exp ((-252732689 / 7397376 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_726 : sigmaPower (726 : Fin 1536) ≤ ((56107968779533 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_727 : sigmaFactor (727 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-378210063 / 11094016 : ℚ) : ℝ) - Real.exp ((-3029553659 / 88752128 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_727 : sigmaPower (727 : Fin 1536) ≤ ((14012261162939 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_728 : sigmaFactor (728 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-377805505 / 11091968 : ℚ) : ℝ) - Real.exp ((-47286195 / 1386496 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_728 : sigmaPower (728 : Fin 1536) ≤ ((13997524691175 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_729 : sigmaFactor (729 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-503201501 / 14786560 : ℚ) : ℝ) - Real.exp ((-1007693577 / 29573120 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_729 : sigmaPower (729 : Fin 1536) ≤ ((111862262212619 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_730 : sigmaFactor (730 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-1507987701 / 44351488 : ℚ) : ℝ) - Real.exp ((-754961603 / 22175744 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_730 : sigmaPower (730 : Fin 1536) ≤ ((111744283329043 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_731 : sigmaFactor (731 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-753185807 / 22171648 : ℚ) : ℝ) - Real.exp ((-3016613523 / 88686592 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_731 : sigmaPower (731 : Fin 1536) ≤ ((111626260854525 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_732 : sigmaFactor (732 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-22799337 / 671744 : ℚ) : ℝ) - Real.exp ((-5707163 / 167936 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_732 : sigmaPower (732 : Fin 1536) ≤ ((55754097382451 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_733 : sigmaFactor (733 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-1503141585 / 44326912 : ℚ) : ℝ) - Real.exp ((-3010152035 / 88653824 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_733 : sigmaPower (733 : Fin 1536) ≤ ((13923760629499 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_734 : sigmaFactor (734 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-1501527643 / 44318720 : ℚ) : ℝ) - Real.exp ((-751730859 / 22159360 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_734 : sigmaPower (734 : Fin 1536) ≤ ((111271931643597 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_735 : sigmaFactor (735 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-31248217 / 923136 : ℚ) : ℝ) - Real.exp ((-1001232089 / 29540352 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_735 : sigmaPower (735 : Fin 1536) ≤ ((111153734563499 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_736 : sigmaFactor (736 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-93643869 / 2768896 : ℚ) : ℝ) - Real.exp ((-2930147 / 86528 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_736 : sigmaPower (736 : Fin 1536) ≤ ((55517746885731 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_737 : sigmaFactor (737 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-1496690107 / 44294144 : ℚ) : ℝ) - Real.exp ((-2997246219 / 88588288 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_737 : sigmaPower (737 : Fin 1536) ≤ ((110917209243235 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_738 : sigmaFactor (738 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-29315275 / 868352 : ℚ) : ℝ) - Real.exp ((-14676585 / 434176 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_738 : sigmaPower (738 : Fin 1536) ≤ ((110798880954547 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_739 : sigmaFactor (739 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-746734329 / 22138880 : ℚ) : ℝ) - Real.exp ((-2990801891 / 88555520 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_739 : sigmaPower (739 : Fin 1536) ≤ ((110680508881107 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_740 : sigmaFactor (740 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-745929503 / 22134784 : ℚ) : ℝ) - Real.exp ((-186723867 / 5533696 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_740 : sigmaPower (740 : Fin 1536) ≤ ((55281046499305 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_741 : sigmaFactor (741 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-496750023 / 14753792 : ℚ) : ℝ) - Real.exp ((-994787761 / 29507584 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_741 : sigmaPower (741 : Fin 1536) ≤ ((110443633282731 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_742 : sigmaFactor (742 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-1488641847 / 44253184 : ℚ) : ℝ) - Real.exp ((-745286531 / 22126592 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_742 : sigmaPower (742 : Fin 1536) ≤ ((55162564854563 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_743 : sigmaFactor (743 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-33796235 / 1005568 : ℚ) : ℝ) - Real.exp ((-270720945 / 8044544 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_743 : sigmaPower (743 : Fin 1536) ≤ ((110206582253435 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_744 : sigmaFactor (744 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-123785629 / 3686400 : ℚ) : ℝ) - Real.exp ((-15493313 / 460800 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_744 : sigmaPower (744 : Fin 1536) ≤ ((110087990891279 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_745 : sigmaFactor (745 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-1483821471 / 44228608 : ℚ) : ℝ) - Real.exp ((-2971503227 / 88457216 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_745 : sigmaPower (745 : Fin 1536) ≤ ((109969355598261 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_746 : sigmaFactor (746 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-1482216109 / 44220416 : ℚ) : ℝ) - Real.exp ((-742072947 / 22110208 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_746 : sigmaPower (746 : Fin 1536) ≤ ((54925338174983 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_747 : sigmaFactor (747 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-246768577 / 7368704 : ℚ) : ℝ) - Real.exp ((-988360593 / 29474816 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_747 : sigmaPower (747 : Fin 1536) ≤ ((109731953121961 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_748 : sigmaFactor (748 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-739503765 / 22102016 : ℚ) : ℝ) - Real.exp ((-185117075 / 5525504 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_748 : sigmaPower (748 : Fin 1536) ≤ ((54806592944897 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_749 : sigmaFactor (749 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-1477404313 / 44195840 : ℚ) : ℝ) - Real.exp ((-2958666051 / 88391680 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_749 : sigmaPower (749 : Fin 1536) ≤ ((27373593657249 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_750 : sigmaFactor (750 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-491933937 / 14729216 : ℚ) : ℝ) - Real.exp ((-246288361 / 7364608 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_750 : sigmaPower (750 : Fin 1536) ≤ ((109375519315079 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_751 : sigmaFactor (751 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-184275003 / 5522432 : ℚ) : ℝ) - Real.exp ((-2952256043 / 88358912 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_751 : sigmaPower (751 : Fin 1536) ≤ ((54628309961769 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_752 : sigmaFactor (752 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-184074869 / 5521408 : ℚ) : ℝ) - Real.exp ((-11519739 / 345088 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_752 : sigmaPower (752 : Fin 1536) ≤ ((109137676429849 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_753 : sigmaFactor (753 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-490332865 / 14721024 : ℚ) : ℝ) - Real.exp ((-981950585 / 29442048 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_753 : sigmaPower (753 : Fin 1536) ≤ ((54509344404735 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_754 : sigmaFactor (754 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-133581723 / 4014080 : ℚ) : ℝ) - Real.exp ((-66878449 / 2007040 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_754 : sigmaPower (754 : Fin 1536) ≤ ((6806228564865 / 17592186044416 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_755 : sigmaFactor (755 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-43170589 / 1298432 : ℚ) : ℝ) - Real.exp ((-172909011 / 5193728 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_755 : sigmaPower (755 : Fin 1536) ≤ ((108780581090381 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_756 : sigmaFactor (756 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-244366969 / 7356416 : ℚ) : ℝ) - Real.exp ((-61172001 / 1839104 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_756 : sigmaPower (756 : Fin 1536) ≤ ((3395670654453 / 8796093022208 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_757 : sigmaFactor (757 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-1464604317 / 44130304 : ℚ) : ℝ) - Real.exp ((-2933060339 / 88260608 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_757 : sigmaPower (757 : Fin 1536) ≤ ((54271148284785 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_758 : sigmaFactor (758 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-1463007535 / 44122112 : ℚ) : ℝ) - Real.exp ((-732466515 / 22061056 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_758 : sigmaPower (758 : Fin 1536) ≤ ((108423087946969 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_759 : sigmaFactor (759 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-121784289 / 3676160 : ℚ) : ℝ) - Real.exp ((-975557737 / 29409280 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_759 : sigmaPower (759 : Fin 1536) ≤ ((108303835050043 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_760 : sigmaFactor (760 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-364954029 / 11026432 : ℚ) : ℝ) - Real.exp ((-45679403 / 1378304 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_760 : sigmaPower (760 : Fin 1536) ≤ ((108184537854121 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_761 : sigmaFactor (761 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-1458221479 / 44097536 : ℚ) : ℝ) - Real.exp ((-2920291803 / 88195072 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_761 : sigmaPower (761 : Fin 1536) ≤ ((108065196334515 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_762 : sigmaFactor (762 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-485542519 / 14696448 : ℚ) : ℝ) - Real.exp ((-243091937 / 7348224 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_762 : sigmaPower (762 : Fin 1536) ≤ ((107945810466517 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_763 : sigmaFactor (763 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-727517175 / 22040576 : ℚ) : ℝ) - Real.exp ((-2913916115 / 88162304 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_763 : sigmaPower (763 : Fin 1536) ≤ ((26956595056351 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_764 : sigmaFactor (764 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-726720929 / 22036480 : ℚ) : ℝ) - Real.exp ((-181920651 / 5509120 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_764 : sigmaPower (764 : Fin 1536) ≤ ((420730099947 / 1099511627776 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_765 : sigmaFactor (765 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-43995457 / 1335296 : ℚ) : ℝ) - Real.exp ((-88107459 / 2670592 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_765 : sigmaPower (765 : Fin 1536) ≤ ((107587386524839 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_766 : sigmaFactor (766 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-1450259019 / 44056576 : ℚ) : ℝ) - Real.exp ((-726090827 / 22028288 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_766 : sigmaPower (766 : Fin 1536) ≤ ((107467823015845 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_767 : sigmaFactor (767 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((107 / 10 : ℚ) : ℝ) * (Real.exp ((-2829431 / 86032 : ℚ) : ℝ) - Real.exp ((-2901181899 / 88096768 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_767 : sigmaPower (767 : Fin 1536) ≤ ((26837053758663 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

end LegendreK6.M2Pilot.Enclosures.Sigma005
