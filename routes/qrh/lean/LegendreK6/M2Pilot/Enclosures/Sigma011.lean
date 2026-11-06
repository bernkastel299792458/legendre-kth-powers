import LegendreK6.M2PilotDefinitions
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp

/-! Generated proposals: every bound is checked by Lean, not by trusting Arb. -/
namespace LegendreK6.M2Pilot.Enclosures.Sigma011
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem sigma_factor_upper_1408 : sigmaFactor (1408 : Fin 1536) ≤ ((46217423 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-9005865 / 606208 : ℚ) : ℝ) - Real.exp ((-70565 / 4736 : ℚ) : ℝ)) ≤ ((46217423 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1408 : sigmaPower (1408 : Fin 1536) ≤ ((2535810600997 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1409 : sigmaFactor (1409 : Fin 1536) ≤ ((23718089 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-575244043 / 38789120 : ℚ) : ℝ) - Real.exp ((-1153873611 / 77578240 : ℚ) : ℝ)) ≤ ((23718089 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1409 : sigmaPower (1409 : Fin 1536) ≤ ((5033061885569 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1410 : sigmaFactor (1410 : Fin 1536) ≤ ((48686709 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-191371147 / 12926976 : ℚ) : ℝ) - Real.exp ((-95967641 / 6463488 : ℚ) : ℝ)) ≤ ((48686709 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1410 : sigmaPower (1410 : Fin 1536) ≤ ((19977945115079 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1411 : sigmaFactor (1411 : Fin 1536) ≤ ((49969835 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-286491777 / 19386368 : ℚ) : ℝ) - Real.exp ((-1149351203 / 77545472 : ℚ) : ℝ)) ≤ ((49969835 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1411 : sigmaPower (1411 : Fin 1536) ≤ ((19823577485081 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1412 : sigmaFactor (1412 : Fin 1536) ≤ ((102572791 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-285927191 / 19382272 : ℚ) : ℝ) - Real.exp ((-71693259 / 4845568 : ℚ) : ℝ)) ≤ ((102572791 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1412 : sigmaPower (1412 : Fin 1536) ≤ ((19669144610945 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1413 : sigmaFactor (1413 : Fin 1536) ≤ ((52637251 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-190241975 / 12918784 : ℚ) : ℝ) - Real.exp ((-381611505 / 25837568 : ℚ) : ℝ)) ≤ ((52637251 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1413 : sigmaPower (1413 : Fin 1536) ≤ ((19514646451299 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1414 : sigmaFactor (1414 : Fin 1536) ≤ ((108046569 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-51781653 / 3522560 : ℚ) : ℝ) - Real.exp ((-25967689 / 1761280 : ℚ) : ℝ)) ≤ ((108046569 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1414 : sigmaPower (1414 : Fin 1536) ≤ ((75625324081 / 1099511627776 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1415 : sigmaFactor (1415 : Fin 1536) ≤ ((110890801 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-142117789 / 9684992 : ℚ) : ℝ) - Real.exp ((-1140323547 / 77479936 : ℚ) : ℝ)) ≤ ((110890801 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1415 : sigmaPower (1415 : Fin 1536) ≤ ((19205454109813 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1416 : sigmaFactor (1416 : Fin 1536) ≤ ((3556533 / 8796093022208 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-47278737 / 3227648 : ℚ) : ℝ) - Real.exp ((-5927449 / 403456 : ℚ) : ℝ)) ≤ ((3556533 / 8796093022208 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1416 : sigmaPower (1416 : Fin 1536) ≤ ((19050759845053 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1417 : sigmaFactor (1417 : Fin 1536) ≤ ((116803235 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-566219247 / 38723584 : ℚ) : ℝ) - Real.exp ((-1135818299 / 77447168 : ℚ) : ℝ)) ≤ ((116803235 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1417 : sigmaPower (1417 : Fin 1536) ≤ ((1181000008059 / 17592186044416 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1418 : sigmaFactor (1418 : Fin 1536) ≤ ((29968823 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-33240845 / 2277376 : ℚ) : ℝ) - Real.exp ((-16670115 / 1138688 : ℚ) : ℝ)) ≤ ((29968823 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1418 : sigmaPower (1418 : Fin 1536) ≤ ((18741174919937 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1419 : sigmaFactor (1419 : Fin 1536) ≤ ((61513613 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-93995033 / 6451200 : ℚ) : ℝ) - Real.exp ((-377106257 / 25804800 : ℚ) : ℝ)) ≤ ((61513613 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1419 : sigmaPower (1419 : Fin 1536) ≤ ((9293142088225 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1420 : sigmaFactor (1420 : Fin 1536) ≤ ((63130545 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-281423373 / 19349504 : ℚ) : ℝ) - Real.exp ((-70566947 / 4837376 : ℚ) : ℝ)) ≤ ((63130545 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1420 : sigmaPower (1420 : Fin 1536) ≤ ((18431327856865 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1421 : sigmaFactor (1421 : Fin 1536) ≤ ((32394747 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-561724009 / 38690816 : ℚ) : ℝ) - Real.exp ((-1126824963 / 77381632 : ℚ) : ℝ)) ≤ ((32394747 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1421 : sigmaPower (1421 : Fin 1536) ≤ ((18276305919529 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1422 : sigmaFactor (1422 : Fin 1536) ≤ ((132983077 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-186867329 / 12894208 : ℚ) : ℝ) - Real.exp ((-93715017 / 6447104 : ℚ) : ℝ)) ≤ ((132983077 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1422 : sigmaPower (1422 : Fin 1536) ≤ ((18121218322753 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1423 : sigmaFactor (1423 : Fin 1536) ≤ ((8529723 / 17592186044416 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-69935085 / 4834304 : ℚ) : ℝ) - Real.exp ((-1122336875 / 77348864 : ℚ) : ℝ)) ≤ ((8529723 / 17592186044416 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1423 : sigmaPower (1423 : Fin 1536) ≤ ((8983032512407 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1424 : sigmaFactor (1424 : Fin 1536) ≤ ((140058731 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-69795011 / 4833280 : ℚ) : ℝ) - Real.exp ((-4375371 / 302080 : ℚ) : ℝ)) ≤ ((140058731 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1424 : sigmaPower (1424 : Fin 1536) ≤ ((1113177873997 / 17592186044416 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1425 : sigmaFactor (1425 : Fin 1536) ≤ ((143734889 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-1535097 / 106496 : ℚ) : ℝ) - Real.exp ((-3079489 / 212992 : ℚ) : ℝ)) ≤ ((143734889 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1425 : sigmaPower (1425 : Fin 1536) ≤ ((4413890289593 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1426 : sigmaFactor (1426 : Fin 1536) ≤ ((36876607 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-556121049 / 38649856 : ℚ) : ℝ) - Real.exp ((-278903867 / 19324928 : ℚ) : ℝ)) ≤ ((36876607 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1426 : sigmaPower (1426 : Fin 1536) ≤ ((4375052626561 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1427 : sigmaFactor (1427 : Fin 1536) ≤ ((9460987 / 17592186044416 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-277501301 / 19320832 : ℚ) : ℝ) - Real.exp ((-1113377859 / 77283328 : ℚ) : ℝ)) ≤ ((9460987 / 17592186044416 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1427 : sigmaPower (1427 : Fin 1536) ≤ ((2168099248213 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1428 : sigmaFactor (1428 : Fin 1536) ≤ ((155345487 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-92314145 / 6438912 : ℚ) : ℝ) - Real.exp ((-23148785 / 1609728 : ℚ) : ℝ)) ≤ ((155345487 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1428 : sigmaPower (1428 : Fin 1536) ≤ ((8594655777425 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1429 : sigmaFactor (1429 : Fin 1536) ≤ ((159418083 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-552767853 / 38625280 : ℚ) : ℝ) - Real.exp ((-1108906931 / 77250560 : ℚ) : ℝ)) ≤ ((159418083 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1429 : sigmaPower (1429 : Fin 1536) ≤ ((17033763171745 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1430 : sigmaFactor (1430 : Fin 1536) ≤ ((163596215 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-551651551 / 38617088 : ℚ) : ℝ) - Real.exp ((-276668403 / 19308544 : ℚ) : ℝ)) ≤ ((163596215 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1430 : sigmaPower (1430 : Fin 1536) ≤ ((16878148794417 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1431 : sigmaFactor (1431 : Fin 1536) ≤ ((20985323 / 35184372088832 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-45877997 / 3217408 : ℚ) : ℝ) - Real.exp ((-368147241 / 25739264 : ℚ) : ℝ)) ≤ ((20985323 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1431 : sigmaPower (1431 : Fin 1536) ≤ ((8361234190429 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1432 : sigmaFactor (1432 : Fin 1536) ≤ ((172279961 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-137355273 / 9650176 : ℚ) : ℝ) - Real.exp ((-17222051 / 1206272 : ℚ) : ℝ)) ≤ ((172279961 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1432 : sigmaPower (1432 : Fin 1536) ≤ ((8283360944513 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1433 : sigmaFactor (1433 : Fin 1536) ≤ ((11049449 / 17592186044416 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-548306935 / 38592512 : ℚ) : ℝ) - Real.exp ((-1099982235 / 77185024 : ℚ) : ℝ)) ≤ ((11049449 / 17592186044416 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1433 : sigmaPower (1433 : Fin 1536) ≤ ((16410909276841 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1434 : sigmaFactor (1434 : Fin 1536) ≤ ((45354791 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-182397831 / 12861440 : ℚ) : ℝ) - Real.exp ((-91479553 / 6430720 : ℚ) : ℝ)) ≤ ((45354791 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1434 : sigmaPower (1434 : Fin 1536) ≤ ((16255030502187 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1435 : sigmaFactor (1435 : Fin 1536) ≤ ((186166887 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-16061199 / 1134592 : ℚ) : ℝ) - Real.exp ((-64442851 / 4538368 : ℚ) : ℝ)) ≤ ((186166887 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1435 : sigmaPower (1435 : Fin 1536) ≤ ((16099085522915 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1436 : sigmaFactor (1436 : Fin 1536) ≤ ((47759353 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-24771307 / 1753088 : ℚ) : ℝ) - Real.exp ((-6211953 / 438272 : ℚ) : ℝ)) ≤ ((47759353 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1436 : sigmaPower (1436 : Fin 1536) ≤ ((15943074296837 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1437 : sigmaFactor (1437 : Fin 1536) ≤ ((49008469 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-181285819 / 12853248 : ℚ) : ℝ) - Real.exp ((-363693473 / 25706496 : ℚ) : ℝ)) ≤ ((49008469 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1437 : sigmaPower (1437 : Fin 1536) ≤ ((15786996781733 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1438 : sigmaFactor (1438 : Fin 1536) ≤ ((201159497 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-542746875 / 38551552 : ℚ) : ℝ) - Real.exp ((-272214635 / 19275776 : ℚ) : ℝ)) ≤ ((201159497 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1438 : sigmaPower (1438 : Fin 1536) ≤ ((7815426467671 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1439 : sigmaFactor (1439 : Fin 1536) ≤ ((103208785 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-33852313 / 2408960 : ℚ) : ℝ) - Real.exp ((-1086638091 / 77086720 : ℚ) : ℝ)) ≤ ((103208785 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1439 : sigmaPower (1439 : Fin 1536) ≤ ((3868660678843 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1440 : sigmaFactor (1440 : Fin 1536) ≤ ((105905739 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-11260997 / 802816 : ℚ) : ℝ) - Real.exp ((-353001 / 25088 : ℚ) : ℝ)) ≤ ((105905739 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1440 : sigmaPower (1440 : Fin 1536) ≤ ((3829591519873 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1441 : sigmaFactor (1441 : Fin 1536) ≤ ((54336171 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-539419419 / 38526976 : ℚ) : ℝ) - Real.exp ((-1082201483 / 77053952 : ℚ) : ℝ)) ≤ ((54336171 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1441 : sigmaPower (1441 : Fin 1536) ≤ ((1895252873167 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1442 : sigmaFactor (1442 : Fin 1536) ≤ ((111510371 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-538311697 / 38518784 : ℚ) : ℝ) - Real.exp ((-269996331 / 19259392 : ℚ) : ℝ)) ≤ ((111510371 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1442 : sigmaPower (1442 : Fin 1536) ≤ ((7502806695251 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1443 : sigmaFactor (1443 : Fin 1536) ≤ ((114421647 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-89534115 / 6418432 : ℚ) : ℝ) - Real.exp ((-359256865 / 25673728 : ℚ) : ℝ)) ≤ ((114421647 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1443 : sigmaPower (1443 : Fin 1536) ≤ ((1856142156569 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1444 : sigmaFactor (1444 : Fin 1536) ≤ ((117408037 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-268049199 / 19251200 : ℚ) : ℝ) - Real.exp ((-67222331 / 4812800 : ℚ) : ℝ)) ≤ ((117408037 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1444 : sigmaPower (1444 : Fin 1536) ≤ ((14692594529011 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1445 : sigmaFactor (1445 : Fin 1536) ≤ ((120471455 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-534992821 / 38494208 : ℚ) : ℝ) - Real.exp ((-1073345427 / 76988416 : ℚ) : ℝ)) ≤ ((120471455 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1445 : sigmaPower (1445 : Fin 1536) ≤ ((14535985177369 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1446 : sigmaFactor (1446 : Fin 1536) ≤ ((247227725 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-177962653 / 12828672 : ℚ) : ℝ) - Real.exp ((-89261249 / 6414336 : ℚ) : ℝ)) ≤ ((247227725 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1446 : sigmaPower (1446 : Fin 1536) ≤ ((14379309155079 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1447 : sigmaFactor (1447 : Fin 1536) ≤ ((253674543 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-12108723 / 874496 : ℚ) : ℝ) - Real.exp ((-97175089 / 6995968 : ℚ) : ℝ)) ≤ ((253674543 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1447 : sigmaPower (1447 : Fin 1536) ≤ ((7111283209779 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1448 : sigmaFactor (1448 : Fin 1536) ≤ ((260287487 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-132920095 / 9617408 : ℚ) : ℝ) - Real.exp ((-16667475 / 1202176 : ℚ) : ℝ)) ≤ ((260287487 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1448 : sigmaPower (1448 : Fin 1536) ≤ ((3516439232047 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1449 : sigmaFactor (1449 : Fin 1536) ≤ ((4172981 / 4398046511104 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-176859221 / 12820480 : ℚ) : ℝ) - Real.exp ((-354837417 / 25640960 : ℚ) : ℝ)) ≤ ((4172981 / 4398046511104 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1449 : sigmaPower (1449 : Fin 1536) ≤ ((1738610079789 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1450 : sigmaFactor (1450 : Fin 1536) ≤ ((274028767 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-529475661 / 38453248 : ℚ) : ℝ) - Real.exp ((-265576883 / 19226624 : ℚ) : ℝ)) ≤ ((274028767 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1450 : sigmaPower (1450 : Fin 1536) ≤ ((13751937507239 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1451 : sigmaFactor (1451 : Fin 1536) ≤ ((281165879 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-264187187 / 19222528 : ℚ) : ℝ) - Real.exp ((-1060104243 / 76890112 : ℚ) : ℝ)) ≤ ((281165879 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1451 : sigmaPower (1451 : Fin 1536) ≤ ((849682968265 / 17592186044416 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1452 : sigmaFactor (1452 : Fin 1536) ≤ ((144243337 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-5169351 / 376832 : ℚ) : ℝ) - Real.exp ((-1296449 / 94208 : ℚ) : ℝ)) ≤ ((144243337 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1452 : sigmaPower (1452 : Fin 1536) ≤ ((1679731318819 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1453 : sigmaFactor (1453 : Fin 1536) ≤ ((147997909 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-526173945 / 38428672 : ℚ) : ℝ) - Real.exp ((-1055701955 / 76857344 : ℚ) : ℝ)) ≤ ((147997909 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1453 : sigmaPower (1453 : Fin 1536) ≤ ((3320176659843 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1454 : sigmaFactor (1454 : Fin 1536) ≤ ((303698097 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-525074803 / 38420480 : ℚ) : ℝ) - Real.exp ((-263375739 / 19210240 : ℚ) : ℝ)) ≤ ((303698097 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1454 : sigmaPower (1454 : Fin 1536) ≤ ((13123495715863 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1455 : sigmaFactor (1455 : Fin 1536) ≤ ((19474901 / 17592186044416 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-21832349 / 1600512 : ℚ) : ℝ) - Real.exp ((-350435129 / 25608192 : ℚ) : ℝ)) ≤ ((19474901 / 17592186044416 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1455 : sigmaPower (1455 : Fin 1536) ≤ ((202597152143 / 4398046511104 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1456 : sigmaFactor (1456 : Fin 1536) ≤ ((319701803 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-65359833 / 4800512 : ℚ) : ℝ) - Real.exp ((-4098083 / 300032 : ℚ) : ℝ)) ≤ ((319701803 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1456 : sigmaPower (1456 : Fin 1536) ≤ ((6404436330163 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1457 : sigmaFactor (1457 : Fin 1536) ≤ ((164006705 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-521781667 / 38395904 : ℚ) : ℝ) - Real.exp ((-1046914539 / 76791808 : ℚ) : ℝ)) ≤ ((164006705 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1457 : sigmaPower (1457 : Fin 1536) ≤ ((12651460442439 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1458 : sigmaFactor (1458 : Fin 1536) ≤ ((42067315 / 35184372088832 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-15778345 / 1163264 : ℚ) : ℝ) - Real.exp ((-7914555 / 581632 : ℚ) : ℝ)) ≤ ((42067315 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1458 : sigmaPower (1458 : Fin 1536) ≤ ((3123495260127 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1459 : sigmaFactor (1459 : Fin 1536) ≤ ((345282549 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-259794909 / 19189760 : ℚ) : ℝ) - Real.exp ((-1042529411 / 76759040 : ℚ) : ℝ)) ≤ ((345282549 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1459 : sigmaPower (1459 : Fin 1536) ≤ ((6168217205755 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1460 : sigmaFactor (1460 : Fin 1536) ≤ ((177125523 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-259247483 / 19185664 : ℚ) : ℝ) - Real.exp ((-65021187 / 4796416 : ℚ) : ℝ)) ≤ ((177125523 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1460 : sigmaPower (1460 : Fin 1536) ≤ ((12178820512389 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1461 : sigmaFactor (1461 : Fin 1536) ≤ ((90862425 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-172466943 / 12787712 : ℚ) : ℝ) - Real.exp ((-346050001 / 25575424 : ℚ) : ℝ)) ≤ ((90862425 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1461 : sigmaPower (1461 : Fin 1536) ≤ ((6010569650025 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1462 : sigmaFactor (1462 : Fin 1536) ≤ ((46610543 / 35184372088832 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-516307407 / 38354944 : ℚ) : ℝ) - Real.exp ((-258990611 / 19177472 : ℚ) : ℝ)) ≤ ((46610543 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1462 : sigmaPower (1462 : Fin 1536) ≤ ((5931695365681 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1463 : sigmaFactor (1463 : Fin 1536) ≤ ((382560953 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-128803675 / 9586688 : ℚ) : ℝ) - Real.exp ((-1033776315 / 76693504 : ℚ) : ℝ)) ≤ ((382560953 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1463 : sigmaPower (1463 : Fin 1536) ≤ ((5852787381579 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1464 : sigmaFactor (1464 : Fin 1536) ≤ ((196242827 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-42843559 / 3194880 : ℚ) : ℝ) - Real.exp ((-5372873 / 399360 : ℚ) : ℝ)) ≤ ((196242827 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1464 : sigmaPower (1464 : Fin 1536) ≤ ((11547691352233 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1465 : sigmaFactor (1465 : Fin 1536) ≤ ((402664727 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-513031431 / 38330368 : ℚ) : ℝ) - Real.exp ((-1029408347 / 76660736 : ℚ) : ℝ)) ≤ ((402664727 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1465 : sigmaPower (1465 : Fin 1536) ≤ ((711858778459 / 17592186044416 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1466 : sigmaFactor (1466 : Fin 1536) ≤ ((12909519 / 8796093022208 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-511940869 / 38322176 : ℚ) : ℝ) - Real.exp ((-256806627 / 19161088 : ℚ) : ℝ)) ≤ ((12909519 / 8796093022208 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1466 : sigmaPower (1466 : Fin 1536) ≤ ((11231722029213 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1467 : sigmaFactor (1467 : Fin 1536) ≤ ((423811893 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-85141837 / 6385664 : ℚ) : ℝ) - Real.exp ((-341682033 / 25542656 : ℚ) : ℝ)) ≤ ((423811893 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1467 : sigmaPower (1467 : Fin 1536) ≤ ((2768409007631 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1468 : sigmaFactor (1468 : Fin 1536) ≤ ((3396823 / 2199023255552 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-254880945 / 19152896 : ℚ) : ℝ) - Real.exp ((-63929195 / 4788224 : ℚ) : ℝ)) ≤ ((3396823 / 2199023255552 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1468 : sigmaPower (1468 : Fin 1536) ≤ ((5457741207963 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1469 : sigmaFactor (1469 : Fin 1536) ≤ ((446055891 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-2720179 / 204800 : ℚ) : ℝ) - Real.exp ((-5458233 / 409600 : ℚ) : ℝ)) ≤ ((446055891 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1469 : sigmaPower (1469 : Fin 1536) ≤ ((5378630571013 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1470 : sigmaFactor (1470 : Fin 1536) ≤ ((114401659 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-169195257 / 12763136 : ℚ) : ℝ) - Real.exp ((-84876121 / 6381568 : ℚ) : ℝ)) ≤ ((114401659 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1470 : sigmaPower (1470 : Fin 1536) ≤ ((1324871520675 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1471 : sigmaFactor (1471 : Fin 1536) ≤ ((117363215 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-15828087 / 1196288 : ℚ) : ℝ) - Real.exp ((-1016338763 / 76562432 : ℚ) : ℝ)) ≤ ((117363215 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1471 : sigmaPower (1471 : Fin 1536) ≤ ((10440615442581 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1472 : sigmaFactor (1472 : Fin 1536) ≤ ((481602023 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-15794141 / 1196032 : ℚ) : ℝ) - Real.exp ((-247599 / 18688 : ℚ) : ℝ)) ≤ ((481602023 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1472 : sigmaPower (1472 : Fin 1536) ≤ ((5141095465035 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1473 : sigmaFactor (1473 : Fin 1536) ≤ ((123515443 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-168108985 / 12754944 : ℚ) : ℝ) - Real.exp ((-337331225 / 25509888 : ℚ) : ℝ)) ≤ ((123515443 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1473 : sigmaPower (1473 : Fin 1536) ≤ ((10123698584327 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1474 : sigmaFactor (1474 : Fin 1536) ≤ ((506839945 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-503242113 / 38256640 : ℚ) : ℝ) - Real.exp ((-252455819 / 19128320 : ℚ) : ℝ)) ≤ ((506839945 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1474 : sigmaPower (1474 : Fin 1536) ≤ ((9965138361777 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1475 : sigmaFactor (1475 : Fin 1536) ≤ ((259972287 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-251078993 / 19124224 : ℚ) : ℝ) - Real.exp ((-1007654307 / 76496896 : ℚ) : ℝ)) ≤ ((259972287 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1475 : sigmaPower (1475 : Fin 1536) ≤ ((9806510218805 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1476 : sigmaFactor (1476 : Fin 1536) ≤ ((133345973 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-83512429 / 6373376 : ℚ) : ℝ) - Real.exp ((-20947641 / 1593344 : ℚ) : ℝ)) ≤ ((133345973 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1476 : sigmaPower (1476 : Fin 1536) ≤ ((4823907055881 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1477 : sigmaFactor (1477 : Fin 1536) ≤ ((273583167 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-499991877 / 38232064 : ℚ) : ℝ) - Real.exp ((-1003320659 / 76464128 : ℚ) : ℝ)) ≤ ((273583167 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1477 : sigmaPower (1477 : Fin 1536) ≤ ((296532812405 / 8796093022208 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1478 : sigmaFactor (1478 : Fin 1536) ≤ ((561300547 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-498909895 / 38223872 : ℚ) : ℝ) - Real.exp ((-250288995 / 19111936 : ℚ) : ℝ)) ≤ ((561300547 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1478 : sigmaPower (1478 : Fin 1536) ≤ ((583138614417 / 17592186044416 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1479 : sigmaFactor (1479 : Fin 1536) ≤ ((287897697 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-41485719 / 3184640 : ℚ) : ℝ) - Real.exp ((-332997577 / 25477120 : ℚ) : ℝ)) ≤ ((287897697 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1479 : sigmaPower (1479 : Fin 1536) ≤ ((9171317569137 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1480 : sigmaFactor (1480 : Fin 1536) ≤ ((590659955 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-11289729 / 868352 : ℚ) : ℝ) - Real.exp ((-1415953 / 108544 : ℚ) : ℝ)) ≤ ((590659955 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1480 : sigmaPower (1480 : Fin 1536) ≤ ((1126543646069 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1481 : sigmaFactor (1481 : Fin 1536) ≤ ((302951769 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-495668239 / 38199296 : ℚ) : ℝ) - Real.exp ((-994670523 / 76398592 : ℚ) : ℝ)) ≤ ((302951769 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1481 : sigmaPower (1481 : Fin 1536) ≤ ((8853312585081 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1482 : sigmaFactor (1482 : Fin 1536) ≤ ((621535681 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-164863039 / 12730368 : ℚ) : ℝ) - Real.exp ((-82709297 / 6365184 : ℚ) : ℝ)) ≤ ((621535681 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1482 : sigmaPower (1482 : Fin 1536) ≤ ((8694207774847 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1483 : sigmaFactor (1483 : Fin 1536) ≤ ((637566159 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-246755355 / 19091456 : ℚ) : ℝ) - Real.exp ((-990354035 / 76365824 : ℚ) : ℝ)) ≤ ((637566159 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1483 : sigmaPower (1483 : Fin 1536) ≤ ((8535034693937 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1484 : sigmaFactor (1484 : Fin 1536) ≤ ((654004989 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-246216509 / 19087360 : ℚ) : ℝ) - Real.exp ((-61762371 / 4771840 : ℚ) : ℝ)) ≤ ((654004989 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1484 : sigmaPower (1484 : Fin 1536) ≤ ((8375793298401 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1485 : sigmaFactor (1485 : Fin 1536) ≤ ((167715609 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-163785347 / 12722176 : ℚ) : ℝ) - Real.exp ((-328681089 / 25444352 : ℚ) : ℝ)) ≤ ((167715609 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1485 : sigmaPower (1485 : Fin 1536) ≤ ((1027060443031 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1486 : sigmaFactor (1486 : Fin 1536) ≤ ((344074511 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-28839987 / 2244608 : ℚ) : ℝ) - Real.exp ((-14468971 / 1122304 : ℚ) : ℝ)) ≤ ((344074511 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1486 : sigmaPower (1486 : Fin 1536) ≤ ((8057105387453 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1487 : sigmaFactor (1487 : Fin 1536) ≤ ((352937763 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-61150529 / 4768768 : ℚ) : ℝ) - Real.exp ((-981738219 / 76300288 : ℚ) : ℝ)) ≤ ((352937763 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1487 : sigmaPower (1487 : Fin 1536) ≤ ((7897658783951 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1488 : sigmaFactor (1488 : Fin 1536) ≤ ((181013249 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-20338725 / 1589248 : ℚ) : ℝ) - Real.exp ((-1275505 / 99328 : ℚ) : ℝ)) ≤ ((181013249 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1488 : sigmaPower (1488 : Fin 1536) ≤ ((7738143689641 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1489 : sigmaFactor (1489 : Fin 1536) ≤ ((742692755 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-487055283 / 38133760 : ℚ) : ℝ) - Real.exp ((-977438891 / 76267520 : ℚ) : ℝ)) ≤ ((742692755 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1489 : sigmaPower (1489 : Fin 1536) ≤ ((1894640015095 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1490 : sigmaFactor (1490 : Fin 1536) ≤ ((761806403 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-485981881 / 38125568 : ℚ) : ℝ) - Real.exp ((-243822843 / 19062784 : ℚ) : ℝ)) ≤ ((761806403 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1490 : sigmaPower (1490 : Fin 1536) ≤ ((7418907851993 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1491 : sigmaFactor (1491 : Fin 1536) ≤ ((781405829 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-7347109 / 577536 : ℚ) : ℝ) - Real.exp ((-29489251 / 2310144 : ℚ) : ℝ)) ≤ ((781405829 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1491 : sigmaPower (1491 : Fin 1536) ≤ ((3629593510131 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1492 : sigmaFactor (1492 : Fin 1536) ≤ ((801503217 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-241918611 / 19054592 : ℚ) : ℝ) - Real.exp ((-60687539 / 4763648 : ℚ) : ℝ)) ≤ ((801503217 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1492 : sigmaPower (1492 : Fin 1536) ≤ ((3549698760467 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1493 : sigmaFactor (1493 : Fin 1536) ≤ ((411055525 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-482765965 / 38100992 : ℚ) : ℝ) - Real.exp ((-968857395 / 76201984 : ℚ) : ℝ)) ≤ ((411055525 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1493 : sigmaPower (1493 : Fin 1536) ≤ ((1734884827429 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1494 : sigmaFactor (1494 : Fin 1536) ≤ ((105405265 / 35184372088832 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-160565141 / 12697600 : ℚ) : ℝ) - Real.exp ((-80559633 / 6348800 : ℚ) : ℝ)) ≤ ((105405265 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1494 : sigmaPower (1494 : Fin 1536) ≤ ((6779612342279 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1495 : sigmaFactor (1495 : Fin 1536) ≤ ((27028423 / 8796093022208 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-120156399 / 9521152 : ℚ) : ℝ) - Real.exp ((-964575227 / 76169216 : ℚ) : ℝ)) ≤ ((27028423 / 8796093022208 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1495 : sigmaPower (1495 : Fin 1536) ≤ ((6619616574253 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1496 : sigmaFactor (1496 : Fin 1536) ≤ ((443563365 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-119889121 / 9519104 : ℚ) : ℝ) - Real.exp ((-15038067 / 1189888 : ℚ) : ℝ)) ≤ ((443563365 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1496 : sigmaPower (1496 : Fin 1536) ≤ ((403721997577 / 17592186044416 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1497 : sigmaFactor (1497 : Fin 1536) ≤ ((909907467 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-159496029 / 12689408 : ℚ) : ℝ) - Real.exp ((-320099593 / 25378816 : ℚ) : ℝ)) ≤ ((909907467 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1497 : sigmaPower (1497 : Fin 1536) ≤ ((6299418458771 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1498 : sigmaFactor (1498 : Fin 1536) ≤ ((466632925 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-477420405 / 38060032 : ℚ) : ℝ) - Real.exp ((-239540675 / 19030016 : ℚ) : ℝ)) ≤ ((466632925 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1498 : sigmaPower (1498 : Fin 1536) ≤ ((1534804005597 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1499 : sigmaFactor (1499 : Fin 1536) ≤ ((957216329 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-238176719 / 19025920 : ℚ) : ℝ) - Real.exp ((-956028051 / 76103680 : ℚ) : ℝ)) ≤ ((957216329 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1499 : sigmaPower (1499 : Fin 1536) ≤ ((5978944607561 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1500 : sigmaFactor (1500 : Fin 1536) ≤ ((981773715 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-79214531 / 6340608 : ℚ) : ℝ) - Real.exp ((-19872809 / 1585152 : ℚ) : ℝ)) ≤ ((981773715 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1500 : sigmaPower (1500 : Fin 1536) ≤ ((2909302084865 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1501 : sigmaFactor (1501 : Fin 1536) ≤ ((503476589 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-474221649 / 38035456 : ℚ) : ℝ) - Real.exp ((-951763043 / 76070912 : ℚ) : ℝ)) ≤ ((503476589 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1501 : sigmaPower (1501 : Fin 1536) ≤ ((5658194664297 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1502 : sigmaFactor (1502 : Fin 1536) ≤ ((1032770267 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-43014257 / 3457024 : ℚ) : ℝ) - Real.exp ((-21582561 / 1728512 : ℚ) : ℝ)) ≤ ((1032770267 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1502 : sigmaPower (1502 : Fin 1536) ≤ ((5497716046625 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1503 : sigmaFactor (1503 : Fin 1536) ≤ ((1059240911 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-578545 / 46592 : ℚ) : ℝ) - Real.exp ((-18578505 / 1490944 : ℚ) : ℝ)) ≤ ((1059240911 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1503 : sigmaPower (1503 : Fin 1536) ≤ ((5337168272041 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1504 : sigmaFactor (1504 : Fin 1536) ≤ ((1086381431 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-29439333 / 2375680 : ℚ) : ℝ) - Real.exp ((-923219 / 74240 : ℚ) : ℝ)) ≤ ((1086381431 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1504 : sigmaPower (1504 : Fin 1536) ≤ ((5176551295829 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1505 : sigmaFactor (1505 : Fin 1536) ≤ ((1114208553 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-469966651 / 38002688 : ℚ) : ℝ) - Real.exp ((-943250187 / 76005376 : ℚ) : ℝ)) ≤ ((1114208553 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1505 : sigmaPower (1505 : Fin 1536) ≤ ((2507932536619 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1506 : sigmaFactor (1506 : Fin 1536) ≤ ((1142739411 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-156301563 / 12664832 : ℚ) : ℝ) - Real.exp ((-78427129 / 6332416 : ℚ) : ℝ)) ≤ ((1142739411 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1506 : sigmaPower (1506 : Fin 1536) ≤ ((4855109559477 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1507 : sigmaFactor (1507 : Fin 1536) ≤ ((1171991563 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-233921721 / 18993152 : ℚ) : ℝ) - Real.exp ((-939002339 / 75972608 : ℚ) : ℝ)) ≤ ((1171991563 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1507 : sigmaPower (1507 : Fin 1536) ≤ ((4694284709717 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1508 : sigmaFactor (1508 : Fin 1536) ≤ ((300495749 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-233391455 / 18989056 : ℚ) : ℝ) - Real.exp ((-58555035 / 4747264 : ℚ) : ℝ)) ≤ ((300495749 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1508 : sigmaPower (1508 : Fin 1536) ≤ ((4533390479091 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1509 : sigmaFactor (1509 : Fin 1536) ≤ ((616366071 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-155241031 / 12656640 : ℚ) : ℝ) - Real.exp ((-311586737 / 25313280 : ℚ) : ℝ)) ≤ ((616366071 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1509 : sigmaPower (1509 : Fin 1536) ≤ ((2186213411345 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1510 : sigmaFactor (1510 : Fin 1536) ≤ ((1264257885 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-464663991 / 37961728 : ℚ) : ℝ) - Real.exp ((-233160323 / 18980864 : ℚ) : ℝ)) ≤ ((1264257885 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1510 : sigmaPower (1510 : Fin 1536) ≤ ((4211393695571 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1511 : sigmaFactor (1511 : Fin 1536) ≤ ((648289785 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-115901401 / 9488384 : ℚ) : ℝ) - Real.exp ((-930523803 / 75907072 : ℚ) : ℝ)) ≤ ((648289785 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1511 : sigmaPower (1511 : Fin 1536) ≤ ((1012572763187 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1512 : sigmaFactor (1512 : Fin 1536) ≤ ((664858511 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-38545661 / 3162112 : ℚ) : ℝ) - Real.exp ((-4835457 / 395264 : ℚ) : ℝ)) ≤ ((664858511 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1512 : sigmaPower (1512 : Fin 1536) ≤ ((1944559424599 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1513 : sigmaFactor (1513 : Fin 1536) ≤ ((340922637 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-41953725 / 3448832 : ℚ) : ℝ) - Real.exp ((-84208465 / 6897664 : ℚ) : ℝ)) ≤ ((340922637 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1513 : sigmaPower (1513 : Fin 1536) ≤ ((3727877039859 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1514 : sigmaFactor (1514 : Fin 1536) ≤ ((1398520957 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-460434733 / 37928960 : ℚ) : ℝ) - Real.exp ((-231044979 / 18964480 : ℚ) : ℝ)) ≤ ((1398520957 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1514 : sigmaPower (1514 : Fin 1536) ≤ ((222910348727 / 17592186044416 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1515 : sigmaFactor (1515 : Fin 1536) ≤ ((358557391 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-76563201 / 6320128 : ℚ) : ℝ) - Real.exp ((-307356049 / 25280512 : ℚ) : ℝ)) ≤ ((358557391 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1515 : sigmaPower (1515 : Fin 1536) ≤ ((1702592211687 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1516 : sigmaFactor (1516 : Fin 1536) ≤ ((1470838211 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-229162197 / 18956288 : ℚ) : ℝ) - Real.exp ((-57497363 / 4739072 : ℚ) : ℝ)) ≤ ((1470838211 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1516 : sigmaPower (1516 : Fin 1536) ≤ ((810933381477 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1517 : sigmaFactor (1517 : Fin 1536) ≤ ((188546159 / 35184372088832 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-457270297 / 37904384 : ℚ) : ℝ) - Real.exp ((-917848899 / 75808768 : ℚ) : ℝ)) ≤ ((188546159 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1517 : sigmaPower (1517 : Fin 1536) ≤ ((96319151313 / 8796093022208 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1518 : sigmaFactor (1518 : Fin 1536) ≤ ((1546845671 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-152072305 / 12632064 : ℚ) : ℝ) - Real.exp ((-76311785 / 6316032 : ℚ) : ℝ)) ≤ ((1546845671 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1518 : sigmaPower (1518 : Fin 1536) ≤ ((2920622326441 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1519 : sigmaFactor (1519 : Fin 1536) ≤ ((396572723 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-56895531 / 4736000 : ℚ) : ℝ) - Real.exp ((-913635371 / 75776000 : ℚ) : ℝ)) ≤ ((396572723 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1519 : sigmaPower (1519 : Fin 1536) ≤ ((2758961933885 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1520 : sigmaFactor (1520 : Fin 1536) ≤ ((813364497 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-3339061 / 278528 : ℚ) : ℝ) - Real.exp ((-209451 / 17408 : ℚ) : ℝ)) ≤ ((813364497 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1520 : sigmaPower (1520 : Fin 1536) ≤ ((2597231619015 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1521 : sigmaFactor (1521 : Fin 1536) ≤ ((1668184627 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-151020353 / 12623872 : ℚ) : ℝ) - Real.exp ((-303142521 / 25247744 : ℚ) : ℝ)) ≤ ((1668184627 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1521 : sigmaPower (1521 : Fin 1536) ≤ ((1217715668227 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1522 : sigmaFactor (1522 : Fin 1536) ≤ ((53458845 / 8796093022208 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-452010537 / 37863424 : ℚ) : ℝ) - Real.exp ((-226831451 / 18931712 : ℚ) : ℝ)) ≤ ((53458845 / 8796093022208 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1522 : sigmaPower (1522 : Fin 1536) ≤ ((1136780520395 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1523 : sigmaFactor (1523 : Fin 1536) ≤ ((1754250103 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-225480365 / 18927616 : ℚ) : ℝ) - Real.exp ((-905225475 / 75710464 : ℚ) : ℝ)) ≤ ((1754250103 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1523 : sigmaPower (1523 : Fin 1536) ≤ ((1055810343285 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1524 : sigmaFactor (1524 : Fin 1536) ≤ ((449728079 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-6816843 / 573440 : ℚ) : ℝ) - Real.exp ((-1710467 / 143360 : ℚ) : ℝ)) ≤ ((449728079 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1524 : sigmaPower (1524 : Fin 1536) ≤ ((1949610228299 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1525 : sigmaFactor (1525 : Fin 1536) ≤ ((461174207 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-448863261 / 37838848 : ℚ) : ℝ) - Real.exp ((-901029107 / 75677696 : ℚ) : ℝ)) ≤ ((461174207 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1525 : sigmaPower (1525 : Fin 1536) ≤ ((55860300639 / 8796093022208 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1526 : sigmaFactor (1526 : Fin 1536) ≤ ((1891631449 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-447815599 / 37830656 : ℚ) : ℝ) - Real.exp ((-224733267 / 18915328 : ℚ) : ℝ)) ≤ ((1891631449 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1526 : sigmaPower (1526 : Fin 1536) ≤ ((1625378817443 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1527 : sigmaFactor (1527 : Fin 1536) ≤ ((1939744669 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-37230721 / 3151872 : ℚ) : ℝ) - Real.exp ((-298946153 / 25214976 : ℚ) : ℝ)) ≤ ((1939744669 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1527 : sigmaPower (1527 : Fin 1536) ≤ ((1463157773675 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1528 : sigmaFactor (1528 : Fin 1536) ≤ ((1989065675 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-111430605 / 9453568 : ℚ) : ℝ) - Real.exp ((-13980395 / 1181696 : ℚ) : ℝ)) ≤ ((1989065675 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1528 : sigmaPower (1528 : Fin 1536) ≤ ((1300866443493 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1529 : sigmaFactor (1529 : Fin 1536) ≤ ((2039624363 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-444676903 / 37806080 : ℚ) : ℝ) - Real.exp ((-892653531 / 75612160 : ℚ) : ℝ)) ≤ ((2039624363 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1529 : sigmaPower (1529 : Fin 1536) ≤ ((569252390603 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1530 : sigmaFactor (1530 : Fin 1536) ≤ ((2091451361 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-147877367 / 12599296 : ℚ) : ℝ) - Real.exp ((-74213601 / 6299648 : ℚ) : ℝ)) ≤ ((2091451361 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1530 : sigmaPower (1530 : Fin 1536) ≤ ((488036370543 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1531 : sigmaFactor (1531 : Fin 1536) ≤ ((268072255 / 35184372088832 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-221294007 / 18894848 : ℚ) : ℝ) - Real.exp ((-888474323 / 75579392 : ℚ) : ℝ)) ≤ ((268072255 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1531 : sigmaPower (1531 : Fin 1536) ≤ ((813570277363 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1532 : sigmaFactor (1532 : Fin 1536) ≤ ((2199036539 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-220772321 / 18890752 : ℚ) : ℝ) - Real.exp ((-55399179 / 4722688 : ℚ) : ℝ)) ≤ ((2199036539 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1532 : sigmaPower (1532 : Fin 1536) ≤ ((650997344229 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1533 : sigmaFactor (1533 : Fin 1536) ≤ ((1127429889 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-146833995 / 12591104 : ℚ) : ℝ) - Real.exp ((-294766945 / 25182208 : ℚ) : ℝ)) ≤ ((1127429889 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1533 : sigmaPower (1533 : Fin 1536) ≤ ((488353895833 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1534 : sigmaFactor (1534 : Fin 1536) ≤ ((2312081479 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-439460043 / 37765120 : ℚ) : ℝ) - Real.exp ((-220554059 / 18882560 : ℚ) : ℝ)) ≤ ((2312081479 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1534 : sigmaPower (1534 : Fin 1536) ≤ ((325639886289 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1535 : sigmaFactor (1535 : Fin 1536) ≤ ((296342023 / 35184372088832 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-311377 / 26816 : ℚ) : ℝ) - Real.exp ((-80012097 / 6864896 : ℚ) : ℝ)) ≤ ((296342023 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1535 : sigmaPower (1535 : Fin 1536) ≤ ((162855269667 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

end LegendreK6.M2Pilot.Enclosures.Sigma011
