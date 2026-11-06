import LegendreK6.M3FarDefinitions
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp

/-! Generated proposals: every bound is checked by Lean, not by trusting Arb. -/
namespace LegendreK6.M3Far.Enclosures.Sigma011
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem sigma_factor_upper_352 : sigmaFactor (352 : Fin 384) ≤ ((4305547 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-47235 / 2368 : ℚ) : ℝ) - Real.exp ((-1505 / 74 : ℚ) : ℝ)) ≤ ((4305547 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_352 : sigmaPower (352 : Fin 384) ≤ ((2535810600997 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_353 : sigmaFactor (353 : Fin 384) ≤ ((633175 / 35184372088832 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-57613 / 2912 : ℚ) : ℝ) - Real.exp ((-117501 / 5824 : ℚ) : ℝ)) ≤ ((633175 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_353 : sigmaPower (353 : Fin 384) ≤ ((19669144610945 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_354 : sigmaFactor (354 : Fin 384) ≤ ((5957053 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-247401 / 12608 : ℚ) : ℝ) - Real.exp ((-126163 / 6304 : ℚ) : ℝ)) ≤ ((5957053 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_354 : sigmaPower (354 : Fin 384) ≤ ((19050759845053 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_355 : sigmaFactor (355 : Fin 384) ≤ ((875369 / 35184372088832 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-367731 / 18896 : ℚ) : ℝ) - Real.exp ((-1500449 / 75584 : ℚ) : ℝ)) ≤ ((875369 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_355 : sigmaPower (355 : Fin 384) ≤ ((18431327856865 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_356 : sigmaFactor (356 : Fin 384) ≤ ((8229289 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-364373 / 18880 : ℚ) : ℝ) - Real.exp ((-92937 / 4720 : ℚ) : ℝ)) ≤ ((8229289 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_356 : sigmaPower (356 : Fin 384) ≤ ((1113177873997 / 17592186044416 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_357 : sigmaFactor (357 : Fin 384) ≤ ((2416655 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-240685 / 12576 : ℚ) : ℝ) - Real.exp ((-491195 / 25152 : ℚ) : ℝ)) ≤ ((2416655 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_357 : sigmaPower (357 : Fin 384) ≤ ((8594655777425 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_358 : sigmaFactor (358 : Fin 384) ≤ ((5675285 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-715389 / 37696 : ℚ) : ℝ) - Real.exp ((-365057 / 18848 : ℚ) : ℝ)) ≤ ((5675285 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_358 : sigmaPower (358 : Fin 384) ≤ ((8283360944513 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_359 : sigmaFactor (359 : Fin 384) ≤ ((6661329 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-177187 / 9416 : ℚ) : ℝ) - Real.exp ((-1446921 / 75328 : ℚ) : ℝ)) ≤ ((6661329 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_359 : sigmaPower (359 : Fin 384) ≤ ((15943074296837 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_360 : sigmaFactor (360 : Fin 384) ≤ ((7815629 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-58511 / 3136 : ℚ) : ℝ) - Real.exp ((-7467 / 392 : ℚ) : ℝ)) ≤ ((7815629 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_360 : sigmaPower (360 : Fin 384) ≤ ((3829591519873 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_361 : sigmaFactor (361 : Fin 384) ≤ ((18332697 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-695541 / 37600 : ℚ) : ℝ) - Real.exp ((-1420457 / 75200 : ℚ) : ℝ)) ≤ ((18332697 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_361 : sigmaPower (361 : Fin 384) ≤ ((14692594529011 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_362 : sigmaFactor (362 : Fin 384) ≤ ((10746269 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-688975 / 37568 : ℚ) : ℝ) - Real.exp ((-351825 / 18784 : ℚ) : ℝ)) ≤ ((10746269 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_362 : sigmaPower (362 : Fin 384) ≤ ((3516439232047 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_363 : sigmaFactor (363 : Fin 384) ≤ ((25187065 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-113739 / 6256 : ℚ) : ℝ) - Real.exp ((-464731 / 25024 : ℚ) : ℝ)) ≤ ((25187065 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_363 : sigmaPower (363 : Fin 384) ≤ ((1679731318819 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_364 : sigmaFactor (364 : Fin 384) ≤ ((14752495 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-337959 / 18752 : ℚ) : ℝ) - Real.exp ((-86321 / 4688 : ℚ) : ℝ)) ≤ ((14752495 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_364 : sigmaPower (364 : Fin 384) ≤ ((6404436330163 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_365 : sigmaFactor (365 : Fin 384) ≤ ((539835 / 4398046511104 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-669427 / 37472 : ℚ) : ℝ) - Real.exp ((-1368129 / 74944 : ℚ) : ℝ)) ≤ ((539835 / 4398046511104 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_365 : sigmaPower (365 : Fin 384) ≤ ((12178820512389 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_366 : sigmaFactor (366 : Fin 384) ≤ ((2527515 / 17592186044416 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-16999 / 960 : ℚ) : ℝ) - Real.exp ((-8687 / 480 : ℚ) : ℝ)) ≤ ((2527515 / 17592186044416 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_366 : sigmaPower (366 : Fin 384) ≤ ((11547691352233 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_367 : sigmaFactor (367 : Fin 384) ≤ ((47316561 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-82065 / 4676 : ℚ) : ℝ) - Real.exp ((-1342265 / 74816 : ℚ) : ℝ)) ≤ ((47316561 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_367 : sigmaPower (367 : Fin 384) ≤ ((5457741207963 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_368 : sigmaFactor (368 : Fin 384) ≤ ((27669985 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-81263 / 4672 : ℚ) : ℝ) - Real.exp ((-5193 / 292 : ℚ) : ℝ)) ≤ ((27669985 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_368 : sigmaPower (368 : Fin 384) ≤ ((5141095465035 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_369 : sigmaFactor (369 : Fin 384) ≤ ((64697947 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-214571 / 12448 : ℚ) : ℝ) - Real.exp ((-438867 / 24896 : ℚ) : ℝ)) ≤ ((64697947 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_369 : sigmaPower (369 : Fin 384) ≤ ((4823907055881 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_370 : sigmaFactor (370 : Fin 384) ≤ ((4725497 / 17592186044416 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-637347 / 37312 : ℚ) : ℝ) - Real.exp ((-325961 / 18656 : ℚ) : ℝ)) ≤ ((4725497 / 17592186044416 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_370 : sigmaPower (370 : Fin 384) ≤ ((1126543646069 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_371 : sigmaFactor (371 : Fin 384) ≤ ((44161051 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-315503 / 18640 : ℚ) : ℝ) - Real.exp ((-1291137 / 74560 : ℚ) : ℝ)) ≤ ((44161051 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_371 : sigmaPower (371 : Fin 384) ≤ ((8375793298401 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_372 : sigmaFactor (372 : Fin 384) ≤ ((25783141 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-104115 / 6208 : ℚ) : ℝ) - Real.exp ((-26635 / 1552 : ℚ) : ℝ)) ≤ ((25783141 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_372 : sigmaPower (372 : Fin 384) ≤ ((7738143689641 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_373 : sigmaFactor (373 : Fin 384) ≤ ((30094441 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-618399 / 37216 : ℚ) : ℝ) - Real.exp ((-1265873 / 74432 : ℚ) : ℝ)) ≤ ((30094441 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_373 : sigmaPower (373 : Fin 384) ≤ ((3549698760467 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_374 : sigmaFactor (374 : Fin 384) ≤ ((35112385 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-612133 / 37184 : ℚ) : ℝ) - Real.exp ((-313329 / 18592 : ℚ) : ℝ)) ≤ ((35112385 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_374 : sigmaPower (374 : Fin 384) ≤ ((403721997577 / 17592186044416 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_375 : sigmaFactor (375 : Fin 384) ≤ ((81900679 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-50491 / 3096 : ℚ) : ℝ) - Real.exp ((-413603 / 24768 : ℚ) : ℝ)) ≤ ((81900679 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_375 : sigmaPower (375 : Fin 384) ≤ ((2909302084865 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_376 : sigmaFactor (376 : Fin 384) ≤ ((11934861 / 17592186044416 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-149919 / 9280 : ℚ) : ℝ) - Real.exp ((-19193 / 1160 : ℚ) : ℝ)) ≤ ((11934861 / 17592186044416 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_376 : sigmaPower (376 : Fin 384) ≤ ((5176551295829 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_377 : sigmaFactor (377 : Fin 384) ≤ ((111262655 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-593485 / 37088 : ℚ) : ℝ) - Real.exp ((-1215945 / 74176 : ℚ) : ℝ)) ≤ ((111262655 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_377 : sigmaPower (377 : Fin 384) ≤ ((4533390479091 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_378 : sigmaFactor (378 : Fin 384) ≤ ((259204917 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-195773 / 12352 : ℚ) : ℝ) - Real.exp ((-100299 / 6176 : ℚ) : ℝ)) ≤ ((259204917 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_378 : sigmaPower (378 : Fin 384) ≤ ((1944559424599 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_379 : sigmaFactor (379 : Fin 384) ≤ ((301806333 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-22353 / 1424 : ℚ) : ℝ) - Real.exp ((-91637 / 5696 : ℚ) : ℝ)) ≤ ((301806333 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_379 : sigmaPower (379 : Fin 384) ≤ ((810933381477 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_380 : sigmaFactor (380 : Fin 384) ≤ ((87816131 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-287531 / 18496 : ℚ) : ℝ) - Real.exp ((-73689 / 4624 : ℚ) : ℝ)) ≤ ((87816131 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_380 : sigmaPower (380 : Fin 384) ≤ ((2597231619015 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_381 : sigmaFactor (381 : Fin 384) ≤ ((408658555 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-189657 / 12320 : ℚ) : ℝ) - Real.exp ((-388939 / 24640 : ℚ) : ℝ)) ≤ ((408658555 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_381 : sigmaPower (381 : Fin 384) ≤ ((1949610228299 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_382 : sigmaFactor (382 : Fin 384) ≤ ((59404153 / 35184372088832 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-562905 / 36928 : ℚ) : ℝ) - Real.exp ((-288665 / 18464 : ℚ) : ℝ)) ≤ ((59404153 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_382 : sigmaPower (382 : Fin 384) ≤ ((1300866443493 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_383 : sigmaFactor (383 : Fin 384) ≤ ((276211927 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-17402 / 1153 : ℚ) : ℝ) - Real.exp ((-1142553 / 73792 : ℚ) : ℝ)) ≤ ((276211927 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_383 : sigmaPower (383 : Fin 384) ≤ ((650997344229 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

end LegendreK6.M3Far.Enclosures.Sigma011
