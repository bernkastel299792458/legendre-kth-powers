import LegendreK6.M3FarDefinitions
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp

/-! Generated proposals: every bound is checked by Lean, not by trusting Arb. -/
namespace LegendreK6.M3Far.Enclosures.Sigma002
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem sigma_factor_upper_64 : sigmaFactor (64 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-117249 / 1472 : ℚ) : ℝ) - Real.exp ((-1841 / 23 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_64 : sigmaPower (64 : Fin 384) ≤ ((81586949771205 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_65 : sigmaFactor (65 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-3737977 / 47072 : ℚ) : ℝ) - Real.exp ((-7512729 / 94144 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_65 : sigmaPower (65 : Fin 384) ≤ ((40693640412735 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_66 : sigmaFactor (66 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-1241337 / 15680 : ℚ) : ℝ) - Real.exp ((-623731 / 7840 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_66 : sigmaPower (66 : Fin 384) ≤ ((81187340221305 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_67 : sigmaFactor (67 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-142695 / 1808 : ℚ) : ℝ) - Real.exp ((-573605 / 7232 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_67 : sigmaPower (67 : Fin 384) ≤ ((161974254807857 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_68 : sigmaFactor (68 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-1848077 / 23488 : ℚ) : ℝ) - Real.exp ((-464313 / 5872 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_68 : sigmaPower (68 : Fin 384) ≤ ((40393320908523 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_69 : sigmaFactor (69 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-1227421 / 15648 : ℚ) : ℝ) - Real.exp ((-2467067 / 31296 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_69 : sigmaPower (69 : Fin 384) ≤ ((161171765805693 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_70 : sigmaFactor (70 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-3668397 / 46912 : ℚ) : ℝ) - Real.exp ((-1843361 / 23456 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_70 : sigmaPower (70 : Fin 384) ≤ ((160769700203995 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_71 : sigmaFactor (71 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-913639 / 11720 : ℚ) : ℝ) - Real.exp ((-7345737 / 93760 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_71 : sigmaPower (71 : Fin 384) ≤ ((80183542853639 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_72 : sigmaFactor (72 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-303395 / 3904 : ℚ) : ℝ) - Real.exp ((-38115 / 488 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_72 : sigmaPower (72 : Fin 384) ≤ ((39990980297689 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_73 : sigmaFactor (73 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-3626949 / 46816 : ℚ) : ℝ) - Real.exp ((-7290473 / 93632 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_73 : sigmaPower (73 : Fin 384) ≤ ((79780102763285 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_74 : sigmaFactor (74 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-3613183 / 46784 : ℚ) : ℝ) - Real.exp ((-1815729 / 23392 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_74 : sigmaPower (74 : Fin 384) ≤ ((159155937583773 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_75 : sigmaFactor (75 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-599907 / 7792 : ℚ) : ℝ) - Real.exp ((-2411803 / 31168 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_75 : sigmaPower (75 : Fin 384) ≤ ((39687779057081 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_76 : sigmaFactor (76 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-1792863 / 23360 : ℚ) : ℝ) - Real.exp ((-450497 / 5840 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_76 : sigmaPower (76 : Fin 384) ≤ ((158345740323073 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_77 : sigmaFactor (77 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-3572035 / 46688 : ℚ) : ℝ) - Real.exp ((-7180545 / 93376 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_77 : sigmaPower (77 : Fin 384) ≤ ((157939808727753 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_78 : sigmaFactor (78 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-1186123 / 15552 : ℚ) : ℝ) - Real.exp ((-596099 / 7776 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_78 : sigmaPower (78 : Fin 384) ≤ ((19691665037371 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_79 : sigmaFactor (79 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-443091 / 5828 : ℚ) : ℝ) - Real.exp ((-7125881 / 93248 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_79 : sigmaPower (79 : Fin 384) ≤ ((78563136945093 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_80 : sigmaFactor (80 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-33953 / 448 : ℚ) : ℝ) - Real.exp ((-2133 / 28 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_80 : sigmaPower (80 : Fin 384) ≤ ((156718668351721 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_81 : sigmaFactor (81 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-1172507 / 15520 : ℚ) : ℝ) - Real.exp ((-2357139 / 31040 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_81 : sigmaPower (81 : Fin 384) ≤ ((156310502530729 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_82 : sigmaFactor (82 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-3503955 / 46528 : ℚ) : ℝ) - Real.exp ((-1761065 / 23264 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_82 : sigmaPower (82 : Fin 384) ≤ ((77950887635597 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_83 : sigmaFactor (83 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-1745207 / 23248 : ℚ) : ℝ) - Real.exp ((-7017153 / 92992 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_83 : sigmaPower (83 : Fin 384) ≤ ((38873121353479 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_84 : sigmaFactor (84 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-579483 / 7744 : ℚ) : ℝ) - Real.exp ((-145627 / 1936 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_84 : sigmaPower (84 : Fin 384) ≤ ((155082631796505 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_85 : sigmaFactor (85 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-3463407 / 46432 : ℚ) : ℝ) - Real.exp ((-6963089 / 92864 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_85 : sigmaPower (85 : Fin 384) ≤ ((38668053313341 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_86 : sigmaFactor (86 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-3449941 / 46400 : ℚ) : ℝ) - Real.exp ((-1734033 / 23200 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_86 : sigmaPower (86 : Fin 384) ≤ ((75322865535 / 137438953472 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_87 : sigmaFactor (87 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-286375 / 3864 : ℚ) : ℝ) - Real.exp ((-2303075 / 30912 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_87 : sigmaPower (87 : Fin 384) ≤ ((153849676711415 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_88 : sigmaFactor (88 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-855771 / 11584 : ℚ) : ℝ) - Real.exp ((-107537 / 1448 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_88 : sigmaPower (88 : Fin 384) ≤ ((76718778182647 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_89 : sigmaFactor (89 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-3409693 / 46304 : ℚ) : ℝ) - Real.exp ((-6855561 / 92608 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_89 : sigmaPower (89 : Fin 384) ≤ ((153024866398791 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_90 : sigmaFactor (90 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-1132109 / 15424 : ℚ) : ℝ) - Real.exp ((-569067 / 7712 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_90 : sigmaPower (90 : Fin 384) ≤ ((152611605630121 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_91 : sigmaFactor (91 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-1691493 / 23120 : ℚ) : ℝ) - Real.exp ((-6802097 / 92480 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_91 : sigmaPower (91 : Fin 384) ≤ ((38049443218557 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_92 : sigmaFactor (92 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-1684835 / 23104 : ℚ) : ℝ) - Real.exp ((-423465 / 5776 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_92 : sigmaPower (92 : Fin 384) ≤ ((151783366942773 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_93 : sigmaFactor (93 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-86061 / 1184 : ℚ) : ℝ) - Real.exp ((-173047 / 2368 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_93 : sigmaPower (93 : Fin 384) ≤ ((151368386644123 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_94 : sigmaFactor (94 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-3343113 / 46144 : ℚ) : ℝ) - Real.exp ((-1680569 / 23072 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_94 : sigmaPower (94 : Fin 384) ≤ ((150952830783339 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_95 : sigmaFactor (95 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-208117 / 2882 : ℚ) : ℝ) - Real.exp ((-6695769 / 92224 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_95 : sigmaPower (95 : Fin 384) ≤ ((150536698162165 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

end LegendreK6.M3Far.Enclosures.Sigma002
