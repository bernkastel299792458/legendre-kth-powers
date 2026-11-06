import LegendreK6.M3FarDefinitions
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp

/-! Generated proposals: every bound is checked by Lean, not by trusting Arb. -/
namespace LegendreK6.M3Far.Enclosures.Sigma003
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem sigma_factor_upper_96 : sigmaFactor (96 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-69097 / 960 : ℚ) : ℝ) - Real.exp ((-2171 / 30 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_96 : sigmaPower (96 : Fin 384) ≤ ((150119987579017 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_97 : sigmaFactor (97 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-3303465 / 46048 : ℚ) : ℝ) - Real.exp ((-6642905 / 92096 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_97 : sigmaPower (97 : Fin 384) ≤ ((149702697828971 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_98 : sigmaFactor (98 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-3290299 / 46016 : ℚ) : ℝ) - Real.exp ((-1654137 / 23008 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_98 : sigmaPower (98 : Fin 384) ≤ ((149284827703751 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_99 : sigmaFactor (99 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-546193 / 7664 : ℚ) : ℝ) - Real.exp ((-2196747 / 30656 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_99 : sigmaPower (99 : Fin 384) ≤ ((74433187995859 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_100 : sigmaFactor (100 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-1632021 / 22976 : ℚ) : ℝ) - Real.exp ((-410249 / 5744 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_100 : sigmaPower (100 : Fin 384) ≤ ((74223670738929 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_101 : sigmaFactor (101 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-3250951 / 45920 : ℚ) : ℝ) - Real.exp ((-6537777 / 91840 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_101 : sigmaPower (101 : Fin 384) ≤ ((148027722943769 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_102 : sigmaFactor (102 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-1079295 / 15296 : ℚ) : ℝ) - Real.exp ((-542635 / 7648 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_102 : sigmaPower (102 : Fin 384) ≤ ((147607519167653 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_103 : sigmaFactor (103 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-806211 / 11464 : ℚ) : ℝ) - Real.exp ((-6485513 / 91712 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_103 : sigmaPower (103 : Fin 384) ≤ ((73593364462149 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_104 : sigmaFactor (104 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-802957 / 11456 : ℚ) : ℝ) - Real.exp ((-100929 / 1432 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_104 : sigmaPower (104 : Fin 384) ≤ ((146765350985073 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_105 : sigmaFactor (105 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-1066279 / 15264 : ℚ) : ℝ) - Real.exp ((-2144483 / 30528 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_105 : sigmaPower (105 : Fin 384) ≤ ((73171692058955 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_106 : sigmaFactor (106 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-245067 / 3520 : ℚ) : ℝ) - Real.exp ((-123221 / 1760 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_106 : sigmaPower (106 : Fin 384) ≤ ((2280012923239 / 4398046511104 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_107 : sigmaFactor (107 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-1586465 / 22864 : ℚ) : ℝ) - Real.exp ((-6381585 / 91456 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_107 : sigmaPower (107 : Fin 384) ≤ ((145497678654261 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_108 : sigmaFactor (108 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-526669 / 7616 : ℚ) : ℝ) - Real.exp ((-132411 / 1904 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_108 : sigmaPower (108 : Fin 384) ≤ ((145073937576361 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_109 : sigmaFactor (109 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-3147123 / 45664 : ℚ) : ℝ) - Real.exp ((-6329921 / 91328 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_109 : sigmaPower (109 : Fin 384) ≤ ((18081200325959 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_110 : sigmaFactor (110 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-3134257 / 45632 : ℚ) : ℝ) - Real.exp ((-1576041 / 22816 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_110 : sigmaPower (110 : Fin 384) ≤ ((144224672498775 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_111 : sigmaFactor (111 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-130059 / 1900 : ℚ) : ℝ) - Real.exp ((-2092819 / 30400 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_111 : sigmaPower (111 : Fin 384) ≤ ((143799145996743 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_112 : sigmaFactor (112 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-388575 / 5696 : ℚ) : ℝ) - Real.exp ((-24425 / 356 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_112 : sigmaPower (112 : Fin 384) ≤ ((143373021845129 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_113 : sigmaFactor (113 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-3095809 / 45536 : ℚ) : ℝ) - Real.exp ((-6227193 / 91072 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_113 : sigmaPower (113 : Fin 384) ≤ ((142946298783955 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_114 : sigmaFactor (114 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-1027681 / 15168 : ℚ) : ℝ) - Real.exp ((-516803 / 7584 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_114 : sigmaPower (114 : Fin 384) ≤ ((35629743887425 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_115 : sigmaFactor (115 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-1535151 / 22736 : ℚ) : ℝ) - Real.exp ((-6176129 / 90944 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_115 : sigmaPower (115 : Fin 384) ≤ ((35522762718821 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_116 : sigmaFactor (116 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-1528793 / 22720 : ℚ) : ℝ) - Real.exp ((-384417 / 5680 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_116 : sigmaPower (116 : Fin 384) ≤ ((70831261745029 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_117 : sigmaFactor (117 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-1014965 / 15136 : ℚ) : ℝ) - Real.exp ((-2041755 / 30272 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_117 : sigmaPower (117 : Fin 384) ≤ ((70616696059897 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_118 : sigmaFactor (118 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-3032229 / 45376 : ℚ) : ℝ) - Real.exp ((-1524977 / 22688 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_118 : sigmaPower (118 : Fin 384) ≤ ((70401827743333 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_119 : sigmaFactor (119 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-58069 / 872 : ℚ) : ℝ) - Real.exp ((-467277 / 6976 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_119 : sigmaPower (119 : Fin 384) ≤ ((140373312309243 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_120 : sigmaFactor (120 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-250581 / 3776 : ℚ) : ℝ) - Real.exp ((-31507 / 472 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_120 : sigmaPower (120 : Fin 384) ≤ ((69971180651237 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_121 : sigmaFactor (121 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-2994381 / 45280 : ℚ) : ℝ) - Real.exp ((-6024137 / 90560 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_121 : sigmaPower (121 : Fin 384) ≤ ((139510801177673 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_122 : sigmaFactor (122 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-2981815 / 45248 : ℚ) : ℝ) - Real.exp ((-1499745 / 22624 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_122 : sigmaPower (122 : Fin 384) ≤ ((8692414415157 / 17592186044416 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_123 : sigmaFactor (123 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-494879 / 7536 : ℚ) : ℝ) - Real.exp ((-1991291 / 30144 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_123 : sigmaPower (123 : Fin 384) ≤ ((138645848401003 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_124 : sigmaFactor (124 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-1478379 / 22592 : ℚ) : ℝ) - Real.exp ((-371801 / 5648 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_124 : sigmaPower (124 : Fin 384) ≤ ((69106226576743 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_125 : sigmaFactor (125 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-2944267 / 45152 : ℚ) : ℝ) - Real.exp ((-5923809 / 90304 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_125 : sigmaPower (125 : Fin 384) ≤ ((137778443596617 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_126 : sigmaFactor (126 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-977267 / 15040 : ℚ) : ℝ) - Real.exp ((-491571 / 7520 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_126 : sigmaPower (126 : Fin 384) ≤ ((34335954605839 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_127 : sigmaFactor (127 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-91230 / 1409 : ℚ) : ℝ) - Real.exp ((-5873945 / 90176 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_127 : sigmaPower (127 : Fin 384) ≤ ((68454288161475 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

end LegendreK6.M3Far.Enclosures.Sigma003
