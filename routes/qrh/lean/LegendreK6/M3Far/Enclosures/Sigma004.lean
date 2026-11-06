import LegendreK6.M3FarDefinitions
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp

/-! Generated proposals: every bound is checked by Lean, not by trusting Arb. -/
namespace LegendreK6.M3Far.Enclosures.Sigma004
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem sigma_factor_upper_128 : sigmaFactor (128 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-45421 / 704 : ℚ) : ℝ) - Real.exp ((-714 / 11 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_128 : sigmaPower (128 : Fin 384) ≤ ((136472715980925 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_129 : sigmaFactor (129 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-964851 / 15008 : ℚ) : ℝ) - Real.exp ((-1941427 / 30016 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_129 : sigmaPower (129 : Fin 384) ≤ ((136036236079067 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_130 : sigmaFactor (130 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-2882187 / 44992 : ℚ) : ℝ) - Real.exp ((-1449881 / 22496 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_130 : sigmaPower (130 : Fin 384) ≤ ((67799567647707 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_131 : sigmaFactor (131 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-1434923 / 22480 : ℚ) : ℝ) - Real.exp ((-5774817 / 89920 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_131 : sigmaPower (131 : Fin 384) ≤ ((8447588269015 / 17592186044416 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_132 : sigmaFactor (132 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-36635 / 576 : ℚ) : ℝ) - Real.exp ((-9215 / 144 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_132 : sigmaPower (132 : Fin 384) ≤ ((134723065776041 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_133 : sigmaFactor (133 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-2845239 / 44896 : ℚ) : ℝ) - Real.exp ((-5725553 / 89792 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_133 : sigmaPower (133 : Fin 384) ≤ ((33571023594381 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_134 : sigmaFactor (134 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-2832973 / 44864 : ℚ) : ℝ) - Real.exp ((-1425249 / 22432 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_134 : sigmaPower (134 : Fin 384) ≤ ((16730562096449 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_135 : sigmaFactor (135 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-235061 / 3736 : ℚ) : ℝ) - Real.exp ((-1892163 / 29888 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_135 : sigmaPower (135 : Fin 384) ≤ ((8337766976083 / 17592186044416 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_136 : sigmaFactor (136 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-702129 / 11200 : ℚ) : ℝ) - Real.exp ((-88313 / 1400 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_136 : sigmaPower (136 : Fin 384) ≤ ((132963417569987 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_137 : sigmaFactor (137 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-2796325 / 44768 : ℚ) : ℝ) - Real.exp ((-5627625 / 89536 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_137 : sigmaPower (137 : Fin 384) ≤ ((8282620830061 / 17592186044416 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_138 : sigmaFactor (138 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-928053 / 14912 : ℚ) : ℝ) - Real.exp ((-466939 / 7456 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_138 : sigmaPower (138 : Fin 384) ≤ ((16509977174731 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_139 : sigmaFactor (139 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-1386009 / 22352 : ℚ) : ℝ) - Real.exp ((-5578961 / 89408 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_139 : sigmaPower (139 : Fin 384) ≤ ((65818534282139 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_140 : sigmaFactor (140 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-1379951 / 22336 : ℚ) : ℝ) - Real.exp ((-347169 / 5584 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_140 : sigmaPower (140 : Fin 384) ≤ ((65596842710029 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_141 : sigmaFactor (141 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-915937 / 14880 : ℚ) : ℝ) - Real.exp ((-1843499 / 29760 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_141 : sigmaPower (141 : Fin 384) ≤ ((130749666601079 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_142 : sigmaFactor (142 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-2735745 / 44608 : ℚ) : ℝ) - Real.exp ((-1376585 / 22304 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_142 : sigmaPower (142 : Fin 384) ≤ ((130305010739319 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_143 : sigmaFactor (143 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-340463 / 5572 : ℚ) : ℝ) - Real.exp ((-5482233 / 89152 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_143 : sigmaPower (143 : Fin 384) ≤ ((129859716462825 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_144 : sigmaFactor (144 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-112987 / 1856 : ℚ) : ℝ) - Real.exp ((-7107 / 116 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_144 : sigmaPower (144 : Fin 384) ≤ ((16176722799463 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_145 : sigmaFactor (145 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-207669 / 3424 : ℚ) : ℝ) - Real.exp ((-418013 / 6848 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_145 : sigmaPower (145 : Fin 384) ≤ ((64483603579053 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_146 : sigmaFactor (146 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-2687731 / 44480 : ℚ) : ℝ) - Real.exp ((-1352553 / 22240 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_146 : sigmaPower (146 : Fin 384) ≤ ((128519989366209 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_147 : sigmaFactor (147 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-445965 / 7408 : ℚ) : ℝ) - Real.exp ((-1795435 / 29632 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_147 : sigmaPower (147 : Fin 384) ≤ ((128072127632207 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_148 : sigmaFactor (148 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-1331937 / 22208 : ℚ) : ℝ) - Real.exp ((-335153 / 5552 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_148 : sigmaPower (148 : Fin 384) ≤ ((63811810282147 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_149 : sigmaFactor (149 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-2651983 / 44384 : ℚ) : ℝ) - Real.exp ((-5338641 / 88768 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_149 : sigmaPower (149 : Fin 384) ≤ ((127174466766651 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_150 : sigmaFactor (150 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-880039 / 14784 : ℚ) : ℝ) - Real.exp ((-442907 / 7392 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_150 : sigmaPower (150 : Fin 384) ≤ ((63362332419715 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_151 : sigmaFactor (151 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-657069 / 11080 : ℚ) : ℝ) - Real.exp ((-5291177 / 88640 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_151 : sigmaPower (151 : Fin 384) ≤ ((31568553344685 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_152 : sigmaFactor (152 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-654115 / 11072 : ℚ) : ℝ) - Real.exp ((-82305 / 1384 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_152 : sigmaPower (152 : Fin 384) ≤ ((125823110976633 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_153 : sigmaFactor (153 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-868223 / 14752 : ℚ) : ℝ) - Real.exp ((-1747971 / 29504 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_153 : sigmaPower (153 : Fin 384) ≤ ((3917854881909 / 8796093022208 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_154 : sigmaFactor (154 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-2592903 / 44224 : ℚ) : ℝ) - Real.exp ((-1305089 / 22112 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_154 : sigmaPower (154 : Fin 384) ≤ ((62459473847999 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_155 : sigmaFactor (155 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-1290581 / 22096 : ℚ) : ℝ) - Real.exp ((-5196849 / 88384 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_155 : sigmaPower (155 : Fin 384) ≤ ((124465883981155 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_156 : sigmaFactor (156 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-428241 / 7360 : ℚ) : ℝ) - Real.exp ((-107779 / 1840 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_156 : sigmaPower (156 : Fin 384) ≤ ((15501520456529 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_157 : sigmaFactor (157 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-2557755 / 44128 : ℚ) : ℝ) - Real.exp ((-5149985 / 88256 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_157 : sigmaPower (157 : Fin 384) ≤ ((30889446320193 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_158 : sigmaFactor (158 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-195853 / 3392 : ℚ) : ℝ) - Real.exp ((-98589 / 1696 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_158 : sigmaPower (158 : Fin 384) ≤ ((30775686858543 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_159 : sigmaFactor (159 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((9387 / 1000 : ℚ) : ℝ) * (Real.exp ((-52801 / 918 : ℚ) : ℝ) - Real.exp ((-1701107 / 29376 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_159 : sigmaPower (159 : Fin 384) ≤ ((30661762168917 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

end LegendreK6.M3Far.Enclosures.Sigma004
