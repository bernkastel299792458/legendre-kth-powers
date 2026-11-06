import LegendreK6.M2PilotDefinitions
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp

/-! Generated proposals: every bound is checked by Lean, not by trusting Arb. -/
namespace LegendreK6.M2Pilot.Enclosures.Sigma001
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem sigma_factor_upper_128 : sigmaFactor (128 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-40791355 / 770048 : ℚ) : ℝ) - Real.exp ((-318945 / 6016 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_128 : sigmaPower (128 : Fin 1536) ≤ ((175672325890339 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_129 : sigmaFactor (129 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-869533401 / 16424960 : ℚ) : ℝ) - Real.exp ((-1740500377 / 32849920 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_129 : sigmaPower (129 : Fin 1536) ≤ ((87788371788727 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_130 : sigmaFactor (130 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-2606554401 / 49266688 : ℚ) : ℝ) - Real.exp ((-1304352203 / 24633344 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_130 : sigmaPower (130 : Fin 1536) ≤ ((87740564738983 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_131 : sigmaFactor (131 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-1302254657 / 24629248 : ℚ) : ℝ) - Real.exp ((-5213317923 / 98516992 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_131 : sigmaPower (131 : Fin 1536) ≤ ((87692741788009 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_132 : sigmaFactor (132 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-433744157 / 8208384 : ℚ) : ℝ) - Real.exp ((-108525593 / 2052096 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_132 : sigmaPower (132 : Fin 1536) ≤ ((87644902927869 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_133 : sigmaFactor (133 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-2600421285 / 49242112 : ℚ) : ℝ) - Real.exp ((-5205140435 / 98484224 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_133 : sigmaPower (133 : Fin 1536) ≤ ((2737407754707 / 4398046511104 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_134 : sigmaFactor (134 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-2598378343 / 49233920 : ℚ) : ℝ) - Real.exp ((-1300263459 / 24616960 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_134 : sigmaPower (134 : Fin 1536) ≤ ((175098354896657 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_135 : sigmaFactor (135 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-216361343 / 4102144 : ℚ) : ℝ) - Real.exp ((-1732322889 / 32817152 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_135 : sigmaPower (135 : Fin 1536) ≤ ((175002581626063 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_136 : sigmaFactor (136 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-648573651 / 12304384 : ℚ) : ℝ) - Real.exp ((-81138827 / 1538048 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_136 : sigmaPower (136 : Fin 1536) ≤ ((174906776473555 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_137 : sigmaFactor (137 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-2592253807 / 49209344 : ℚ) : ℝ) - Real.exp ((-5188802619 / 98418688 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_137 : sigmaPower (137 : Fin 1536) ≤ ((87405469711605 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_138 : sigmaFactor (138 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-78491325 / 1490944 : ℚ) : ℝ) - Real.exp ((-39278195 / 745472 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_138 : sigmaPower (138 : Fin 1536) ≤ ((21839383807387 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_139 : sigmaFactor (139 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-1294087179 / 24596480 : ℚ) : ℝ) - Real.exp ((-5180642291 / 98385920 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_139 : sigmaPower (139 : Fin 1536) ≤ ((43654792391317 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_140 : sigmaFactor (140 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-1293067853 / 24592384 : ℚ) : ℝ) - Real.exp ((-323535267 / 6148096 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_140 : sigmaPower (140 : Fin 1536) ≤ ((174523236725773 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_141 : sigmaFactor (141 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-861365923 / 16392192 : ℚ) : ℝ) - Real.exp ((-1724162561 / 32784384 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_141 : sigmaPower (141 : Fin 1536) ≤ ((174427271924645 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_142 : sigmaFactor (142 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-2582060547 / 49168384 : ℚ) : ℝ) - Real.exp ((-1292103131 / 24584192 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_142 : sigmaPower (142 : Fin 1536) ≤ ((174331275145909 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_143 : sigmaFactor (143 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-18970765 / 361472 : ℚ) : ℝ) - Real.exp ((-303784635 / 5783552 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_143 : sigmaPower (143 : Fin 1536) ≤ ((43558811593395 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_144 : sigmaFactor (144 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-107416177 / 2048000 : ℚ) : ℝ) - Real.exp ((-6719097 / 128000 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_144 : sigmaPower (144 : Fin 1536) ≤ ((43534796397915 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_145 : sigmaFactor (145 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-2575953171 / 49143808 : ℚ) : ℝ) - Real.exp ((-5156195627 / 98287616 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_145 : sigmaPower (145 : Fin 1536) ≤ ((174043092784141 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_146 : sigmaFactor (146 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-2573918809 / 49135616 : ℚ) : ℝ) - Real.exp ((-1288031547 / 24567808 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_146 : sigmaPower (146 : Fin 1536) ≤ ((86973483967503 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_147 : sigmaFactor (147 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-428647527 / 8187904 : ℚ) : ℝ) - Real.exp ((-1716019393 / 32751616 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_147 : sigmaPower (147 : Fin 1536) ≤ ((86925405514113 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_148 : sigmaFactor (148 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-1284926115 / 24559616 : ℚ) : ℝ) - Real.exp ((-321499475 / 6139904 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_148 : sigmaPower (148 : Fin 1536) ≤ ((173754622047761 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_149 : sigmaFactor (149 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-233438183 / 4464640 : ℚ) : ℝ) - Real.exp ((-467266041 / 8929280 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_149 : sigmaPower (149 : Fin 1536) ≤ ((86829200488781 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_150 : sigmaFactor (150 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-855262837 / 16367616 : ℚ) : ℝ) - Real.exp ((-427988561 / 8183808 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_150 : sigmaPower (150 : Fin 1536) ≤ ((86781073900783 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_151 : sigmaFactor (151 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-640939431 / 12273664 : ℚ) : ℝ) - Real.exp ((-5131800443 / 98189312 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_151 : sigmaPower (151 : Fin 1536) ≤ ((173465862503703 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_152 : sigmaFactor (152 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-640431913 / 12271616 : ℚ) : ℝ) - Real.exp ((-80120931 / 1533952 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_152 : sigmaPower (152 : Fin 1536) ≤ ((86684772533945 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_153 : sigmaFactor (153 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-853232765 / 16359424 : ℚ) : ℝ) - Real.exp ((-1707893385 / 32718848 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_153 : sigmaPower (153 : Fin 1536) ≤ ((86636597739017 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_154 : sigmaFactor (154 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-2557669653 / 49070080 : ℚ) : ℝ) - Real.exp ((-1279905539 / 24535040 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_154 : sigmaPower (154 : Fin 1536) ≤ ((173176813718031 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_155 : sigmaFactor (155 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-1277820863 / 24530944 : ℚ) : ℝ) - Real.exp ((-5115565587 / 98123776 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_155 : sigmaPower (155 : Fin 1536) ≤ ((173080399771767 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_156 : sigmaFactor (156 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-425602419 / 8175616 : ℚ) : ℝ) - Real.exp ((-106489801 / 2043904 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_156 : sigmaPower (156 : Fin 1536) ≤ ((43245988405779 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_157 : sigmaFactor (157 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-2551588017 / 49045504 : ℚ) : ℝ) - Real.exp ((-5107456739 / 98091008 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_157 : sigmaPower (157 : Fin 1536) ≤ ((86443737627971 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_158 : sigmaFactor (158 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-2549562235 / 49037312 : ℚ) : ℝ) - Real.exp ((-1275851115 / 24518656 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_158 : sigmaPower (158 : Fin 1536) ≤ ((172790964654097 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_159 : sigmaFactor (159 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-53073691 / 1021440 : ℚ) : ℝ) - Real.exp ((-1699784537 / 32686080 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_159 : sigmaPower (159 : Fin 1536) ≤ ((86347210900713 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_160 : sigmaFactor (160 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-850773 / 16384 : ℚ) : ℝ) - Real.exp ((-26609 / 512 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_160 : sigmaPower (160 : Fin 1536) ≤ ((172597846681757 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_161 : sigmaFactor (161 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-2543489179 / 49012736 : ℚ) : ℝ) - Real.exp ((-5091256203 / 98025472 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_161 : sigmaPower (161 : Fin 1536) ≤ ((86250619639457 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_162 : sigmaFactor (162 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-847155419 / 16334848 : ℚ) : ℝ) - Real.exp ((-423934137 / 8167424 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_162 : sigmaPower (162 : Fin 1536) ≤ ((172404599576705 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_163 : sigmaFactor (163 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-1269722025 / 24498176 : ℚ) : ℝ) - Real.exp ((-5083164515 / 97992704 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_163 : sigmaPower (163 : Fin 1536) ≤ ((172307927558929 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_164 : sigmaFactor (164 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-1268711279 / 24494080 : ℚ) : ℝ) - Real.exp ((-317445051 / 6123520 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_164 : sigmaPower (164 : Fin 1536) ≤ ((86105611604687 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_165 : sigmaFactor (165 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-845133927 / 16326656 : ℚ) : ℝ) - Real.exp ((-1691692849 / 32653312 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_165 : sigmaPower (165 : Fin 1536) ≤ ((86057243255909 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_166 : sigmaFactor (166 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-2533381719 / 48971776 : ℚ) : ℝ) - Real.exp ((-1267759427 / 24485888 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_166 : sigmaPower (166 : Fin 1536) ≤ ((43004429362507 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_167 : sigmaFactor (167 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-632840593 / 12240896 : ℚ) : ℝ) - Real.exp ((-5066998299 / 97927168 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_167 : sigmaPower (167 : Fin 1536) ≤ ((85960458003879 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_168 : sigmaFactor (168 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-210778645 / 4079616 : ℚ) : ℝ) - Real.exp ((-26369585 / 509952 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_168 : sigmaPower (168 : Fin 1536) ≤ ((85912041084377 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_169 : sigmaFactor (169 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-2527325823 / 48947200 : ℚ) : ℝ) - Real.exp ((-5058923771 / 97894400 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_169 : sigmaPower (169 : Fin 1536) ≤ ((85863607958375 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_170 : sigmaFactor (170 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-2525308621 / 48939008 : ℚ) : ℝ) - Real.exp ((-1263722163 / 24469504 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_170 : sigmaPower (170 : Fin 1536) ≤ ((42907579308867 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_171 : sigmaFactor (171 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-38231699 / 741376 : ℚ) : ℝ) - Real.exp ((-153056211 / 2965504 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_171 : sigmaPower (171 : Fin 1536) ≤ ((171533386108621 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_172 : sigmaFactor (172 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-1260638181 / 24461312 : ℚ) : ℝ) - Real.exp ((-315426419 / 6115328 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_172 : sigmaPower (172 : Fin 1536) ≤ ((171436422519909 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_173 : sigmaFactor (173 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-2519261305 / 48914432 : ℚ) : ℝ) - Real.exp ((-5042791875 / 97828864 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_173 : sigmaPower (173 : Fin 1536) ≤ ((171339426453023 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_174 : sigmaFactor (174 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-839082321 / 16302080 : ℚ) : ℝ) - Real.exp ((-419896873 / 8151040 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_174 : sigmaPower (174 : Fin 1536) ≤ ((85621198945821 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_175 : sigmaFactor (175 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-314404167 / 6112256 : ℚ) : ℝ) - Real.exp ((-5034734507 / 97796096 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_175 : sigmaPower (175 : Fin 1536) ≤ ((171145336819435 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_176 : sigmaFactor (176 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-314152553 / 6111232 : ℚ) : ℝ) - Real.exp ((-19651203 / 381952 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_176 : sigmaPower (176 : Fin 1536) ≤ ((42762060805015 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_177 : sigmaFactor (177 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-49239377 / 958464 : ℚ) : ℝ) - Real.exp ((-98562409 / 1916928 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_177 : sigmaPower (177 : Fin 1536) ≤ ((170951117077161 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_178 : sigmaFactor (178 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-2509196745 / 48873472 : ℚ) : ℝ) - Real.exp ((-1255664795 / 24436736 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_178 : sigmaPower (178 : Fin 1536) ≤ ((21356744796797 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_179 : sigmaFactor (179 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-1253592989 / 24432640 : ℚ) : ℝ) - Real.exp ((-5018636931 / 97730560 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_179 : sigmaPower (179 : Fin 1536) ≤ ((5336148971729 / 8796093022208 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_180 : sigmaFactor (180 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-417529321 / 8142848 : ℚ) : ℝ) - Real.exp ((-104471169 / 2035712 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_180 : sigmaPower (180 : Fin 1536) ≤ ((170659543223631 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_181 : sigmaFactor (181 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-2503166589 / 48848896 : ℚ) : ℝ) - Real.exp ((-5010596723 / 97697792 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_181 : sigmaPower (181 : Fin 1536) ≤ ((21320285842861 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_182 : sigmaFactor (182 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-227377997 / 4440064 : ℚ) : ℝ) - Real.exp ((-113785881 / 2220032 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_182 : sigmaPower (182 : Fin 1536) ≤ ((85232498818345 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_183 : sigmaFactor (183 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-208262505 / 4069376 : ℚ) : ℝ) - Real.exp ((-1667520745 / 32555008 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_183 : sigmaPower (183 : Fin 1536) ≤ ((85183837944309 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_184 : sigmaFactor (184 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-624285717 / 12206080 : ℚ) : ℝ) - Real.exp ((-78102299 / 1525760 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_184 : sigmaPower (184 : Fin 1536) ≤ ((170270321482241 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_185 : sigmaFactor (185 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-2495136391 / 48816128 : ℚ) : ℝ) - Real.exp ((-4994533467 / 97632256 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_185 : sigmaPower (185 : Fin 1536) ≤ ((85086467200559 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_186 : sigmaFactor (186 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-831043543 / 16269312 : ℚ) : ℝ) - Real.exp ((-415876769 / 8134656 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_186 : sigmaPower (186 : Fin 1536) ≤ ((42518878657199 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_187 : sigmaFactor (187 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-1245562791 / 24399872 : ℚ) : ℝ) - Real.exp ((-4986510419 / 97599488 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_187 : sigmaPower (187 : Fin 1536) ≤ ((169978062148811 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_188 : sigmaFactor (188 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-1244560625 / 24395776 : ℚ) : ℝ) - Real.exp ((-311406315 / 6098944 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_188 : sigmaPower (188 : Fin 1536) ≤ ((84940288472345 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_189 : sigmaFactor (189 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-829039211 / 16261120 : ℚ) : ℝ) - Real.exp ((-1659497697 / 32522240 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_189 : sigmaPower (189 : Fin 1536) ≤ ((84891529499973 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_190 : sigmaFactor (190 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-2485114731 / 48775168 : ℚ) : ℝ) - Real.exp ((-1243621643 / 24387584 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_190 : sigmaPower (190 : Fin 1536) ≤ ((169685508298083 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_191 : sigmaFactor (191 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-77597267 / 1523968 : ℚ) : ℝ) - Real.exp ((-4970481483 / 97533952 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_191 : sigmaPower (191 : Fin 1536) ≤ ((2649811325353 / 4398046511104 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_192 : sigmaFactor (192 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-25844907 / 507904 : ℚ) : ℝ) - Real.exp ((-404173 / 7936 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_192 : sigmaPower (192 : Fin 1536) ≤ ((169490308556955 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_193 : sigmaFactor (193 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-225373665 / 4431872 : ℚ) : ℝ) - Real.exp ((-451134145 / 8863744 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_193 : sigmaPower (193 : Fin 1536) ≤ ((169392659484641 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_194 : sigmaFactor (194 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-145712369 / 2867200 : ℚ) : ℝ) - Real.exp ((-72918747 / 1433600 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_194 : sigmaPower (194 : Fin 1536) ≤ ((84647488794555 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_195 : sigmaFactor (195 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-412518491 / 8122368 : ℚ) : ℝ) - Real.exp ((-1651491809 / 32489472 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_195 : sigmaPower (195 : Fin 1536) ≤ ((169197262853809 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_196 : sigmaFactor (196 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-1236556167 / 24363008 : ℚ) : ℝ) - Real.exp ((-309404843 / 6090752 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_196 : sigmaPower (196 : Fin 1536) ≤ ((84549757631087 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_197 : sigmaFactor (197 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-2471114437 / 48717824 : ℚ) : ℝ) - Real.exp ((-4946480979 / 97435648 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_197 : sigmaPower (197 : Fin 1536) ≤ ((2640652106213 / 4398046511104 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_198 : sigmaFactor (198 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-823039085 / 16236544 : ℚ) : ℝ) - Real.exp ((-411873825 / 8118272 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_198 : sigmaPower (198 : Fin 1536) ≤ ((42225980360899 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_199 : sigmaFactor (199 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-616780197 / 12175360 : ℚ) : ℝ) - Real.exp ((-4938492251 / 97402880 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_199 : sigmaPower (199 : Fin 1536) ≤ ((84403037591735 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_200 : sigmaFactor (200 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-616281259 / 12173312 : ℚ) : ℝ) - Real.exp ((-77101563 / 1521664 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_200 : sigmaPower (200 : Fin 1536) ≤ ((168708196000645 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_201 : sigmaFactor (201 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-821043333 / 16228352 : ℚ) : ℝ) - Real.exp ((-1643503081 / 32456704 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_201 : sigmaPower (201 : Fin 1536) ≤ ((84305141939251 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_202 : sigmaFactor (202 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-2461135677 / 48676864 : ℚ) : ℝ) - Real.exp ((-1231629971 / 24338432 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_202 : sigmaPower (202 : Fin 1536) ≤ ((168512338800411 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_203 : sigmaFactor (203 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-1229571035 / 24334336 : ℚ) : ℝ) - Real.exp ((-4922531955 / 97337344 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_203 : sigmaPower (203 : Fin 1536) ≤ ((84207180374865 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_204 : sigmaFactor (204 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-37229533 / 737280 : ℚ) : ℝ) - Real.exp ((-9315427 / 184320 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_204 : sigmaPower (204 : Fin 1536) ≤ ((168316349709807 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_205 : sigmaFactor (205 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-2455157001 / 48652288 : ℚ) : ℝ) - Real.exp ((-4914560387 / 97304576 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_205 : sigmaPower (205 : Fin 1536) ≤ ((168218305663977 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_206 : sigmaFactor (206 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-2453165539 / 48644096 : ℚ) : ℝ) - Real.exp ((-1227644187 / 24322048 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_206 : sigmaPower (206 : Fin 1536) ≤ ((168120228595565 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_207 : sigmaFactor (207 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-102132283 / 2026496 : ℚ) : ℝ) - Real.exp ((-1635531513 / 32423936 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_207 : sigmaPower (207 : Fin 1536) ≤ ((42005529621971 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_208 : sigmaFactor (208 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-306148095 / 6078464 : ℚ) : ℝ) - Real.exp ((-19150835 / 379904 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_208 : sigmaPower (208 : Fin 1536) ≤ ((167923975324237 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_209 : sigmaFactor (209 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-2447195443 / 48619520 : ℚ) : ℝ) - Real.exp ((-4898634411 / 97239040 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_209 : sigmaPower (209 : Fin 1536) ≤ ((167825799087915 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_210 : sigmaFactor (210 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-815068947 / 16203776 : ℚ) : ℝ) - Real.exp ((-407888041 / 8101888 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_210 : sigmaPower (210 : Fin 1536) ≤ ((83863794881099 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_211 : sigmaFactor (211 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-71859381 / 1429504 : ℚ) : ℝ) - Real.exp ((-287687059 / 5718016 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_211 : sigmaPower (211 : Fin 1536) ≤ ((83814673665177 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_212 : sigmaFactor (212 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-1220615891 / 24297472 : ℚ) : ℝ) - Real.exp ((-305419059 / 6074368 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_212 : sigmaPower (212 : Fin 1536) ≤ ((167531071775639 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_213 : sigmaFactor (213 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-813081775 / 16195584 : ℚ) : ℝ) - Real.exp ((-1627577105 / 32391168 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_213 : sigmaPower (213 : Fin 1536) ≤ ((167432763081301 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_214 : sigmaFactor (214 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-2437259583 / 48578560 : ℚ) : ℝ) - Real.exp ((-1219689779 / 24289280 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_214 : sigmaPower (214 : Fin 1536) ≤ ((83667210615287 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_215 : sigmaFactor (215 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-5031559 / 100352 : ℚ) : ℝ) - Real.exp ((-40287507 / 802816 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_215 : sigmaPower (215 : Fin 1536) ≤ ((20904505775835 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_216 : sigmaFactor (216 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-202774187 / 4046848 : ℚ) : ℝ) - Real.exp ((-25368849 / 505856 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_216 : sigmaPower (216 : Fin 1536) ≤ ((167137637992833 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_217 : sigmaFactor (217 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-2431306647 / 48553984 : ℚ) : ℝ) - Real.exp ((-4866851099 / 97107968 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_217 : sigmaPower (217 : Fin 1536) ≤ ((20879899571529 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_218 : sigmaFactor (218 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-2429323765 / 48545792 : ℚ) : ℝ) - Real.exp ((-1215721155 / 24272896 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_218 : sigmaPower (218 : Fin 1536) ≤ ((83470360964033 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_219 : sigmaFactor (219 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-404556933 / 8089600 : ℚ) : ℝ) - Real.exp ((-1619639857 / 32358400 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_219 : sigmaPower (219 : Fin 1536) ≤ ((166842214043515 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_220 : sigmaFactor (220 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-1212680073 / 24264704 : ℚ) : ℝ) - Real.exp ((-303434747 / 6066176 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_220 : sigmaPower (220 : Fin 1536) ≤ ((10421479556359 / 17592186044416 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_221 : sigmaFactor (221 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-2423379409 / 48521216 : ℚ) : ℝ) - Real.exp ((-4850993763 / 97042432 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_221 : sigmaPower (221 : Fin 1536) ≤ ((166645098485909 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_222 : sigmaFactor (222 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-807133129 / 16171008 : ℚ) : ℝ) - Real.exp ((-403919417 / 8085504 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_222 : sigmaPower (222 : Fin 1536) ≤ ((166546490779153 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_223 : sigmaFactor (223 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-151213755 / 3031552 : ℚ) : ℝ) - Real.exp ((-4843073675 / 97009664 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_223 : sigmaPower (223 : Fin 1536) ≤ ((650186913143 / 1099511627776 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_224 : sigmaFactor (224 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-151090093 / 3031040 : ℚ) : ℝ) - Real.exp ((-4725699 / 94720 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_224 : sigmaPower (224 : Fin 1536) ≤ ((166349175425397 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_225 : sigmaFactor (225 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-805154537 / 16162816 : ℚ) : ℝ) - Real.exp ((-1611719769 / 32325632 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_225 : sigmaPower (225 : Fin 1536) ≤ ((166250467744629 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_226 : sigmaFactor (226 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-219407859 / 4407296 : ℚ) : ℝ) - Real.exp ((-109800097 / 2203648 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_226 : sigmaPower (226 : Fin 1536) ≤ ((166151726705401 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_227 : sigmaFactor (227 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-1205755001 / 24236032 : ℚ) : ℝ) - Real.exp ((-4827250659 / 96944128 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_227 : sigmaPower (227 : Fin 1536) ≤ ((10378309518175 / 17592186044416 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_228 : sigmaFactor (228 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-23622885 / 475136 : ℚ) : ℝ) - Real.exp ((-5910905 / 118784 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_228 : sigmaPower (228 : Fin 1536) ≤ ((165954144483903 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_229 : sigmaFactor (229 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-2407559253 / 48455680 : ℚ) : ℝ) - Real.exp ((-4819347731 / 96911360 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_229 : sigmaPower (229 : Fin 1536) ≤ ((165855303267773 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_230 : sigmaFactor (230 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-2405584951 / 48447488 : ℚ) : ℝ) - Real.exp ((-1203849603 / 24223744 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_230 : sigmaPower (230 : Fin 1536) ≤ ((82878214312731 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_231 : sigmaFactor (231 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-200300947 / 4036608 : ℚ) : ℝ) - Real.exp ((-1603816841 / 32292864 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_231 : sigmaPower (231 : Fin 1536) ≤ ((165657520540011 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_232 : sigmaFactor (232 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-600409623 / 12107776 : ℚ) : ℝ) - Real.exp ((-75117251 / 1513472 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_232 : sigmaPower (232 : Fin 1536) ≤ ((82779289497225 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_233 : sigmaFactor (233 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-2399666335 / 48422912 : ℚ) : ℝ) - Real.exp ((-4803559035 / 96845824 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_233 : sigmaPower (233 : Fin 1536) ≤ ((82729801985899 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_234 : sigmaFactor (234 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-799231631 / 16138240 : ℚ) : ℝ) - Real.exp ((-399967953 / 8069120 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_234 : sigmaPower (234 : Fin 1536) ≤ ((165360595455059 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_235 : sigmaFactor (235 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-1197862083 / 24203264 : ℚ) : ℝ) - Real.exp ((-4795673267 / 96813056 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_235 : sigmaPower (235 : Fin 1536) ≤ ((165261553427231 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_236 : sigmaFactor (236 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-1196877077 / 24199168 : ℚ) : ℝ) - Real.exp ((-299483283 / 6049792 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_236 : sigmaPower (236 : Fin 1536) ≤ ((165162477871295 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_237 : sigmaFactor (237 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-72478329 / 1466368 : ℚ) : ℝ) - Real.exp ((-145084643 / 2932736 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_237 : sigmaPower (237 : Fin 1536) ≤ ((10316460548139 / 17592186044416 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_238 : sigmaFactor (238 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-2389816275 / 48381952 : ℚ) : ℝ) - Real.exp ((-1195963835 / 24190976 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_238 : sigmaPower (238 : Fin 1536) ≤ ((164964226106979 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_239 : sigmaFactor (239 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-298481051 / 6046720 : ℚ) : ℝ) - Real.exp ((-4779918891 / 96747520 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_239 : sigmaPower (239 : Fin 1536) ≤ ((164865049864509 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_240 : sigmaFactor (240 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-99411719 / 2015232 : ℚ) : ℝ) - Real.exp ((-6218729 / 125952 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_240 : sigmaPower (240 : Fin 1536) ≤ ((82382920012875 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_241 : sigmaFactor (241 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-2383914819 / 48357376 : ℚ) : ℝ) - Real.exp ((-4772050283 / 96714752 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_241 : sigmaPower (241 : Fin 1536) ≤ ((82333298286815 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_242 : sigmaFactor (242 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-2381949097 / 48349184 : ℚ) : ℝ) - Real.exp ((-1192029531 / 24174592 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_242 : sigmaPower (242 : Fin 1536) ≤ ((164567319491061 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_243 : sigmaFactor (243 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-396664015 / 8056832 : ℚ) : ℝ) - Real.exp ((-1588062465 / 32227328 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_243 : sigmaPower (243 : Fin 1536) ≤ ((82234004380473 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_244 : sigmaFactor (244 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-1189009899 / 24166400 : ℚ) : ℝ) - Real.exp ((-297516131 / 6041600 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_244 : sigmaPower (244 : Fin 1536) ≤ ((82184332183089 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_245 : sigmaFactor (245 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-139768013 / 2842624 : ℚ) : ℝ) - Real.exp ((-279784131 / 5685248 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_245 : sigmaPower (245 : Fin 1536) ≤ ((164269286289635 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_246 : sigmaFactor (246 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-791364453 / 16105472 : ℚ) : ℝ) - Real.exp ((-396033649 / 8052736 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_246 : sigmaPower (246 : Fin 1536) ≤ ((20521234314273 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_247 : sigmaFactor (247 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-593032803 / 12077056 : ℚ) : ℝ) - Real.exp ((-4748478779 / 96616448 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_247 : sigmaPower (247 : Fin 1536) ≤ ((164070429022683 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_248 : sigmaFactor (248 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-53867495 / 1097728 : ℚ) : ℝ) - Real.exp ((-6739425 / 137216 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_248 : sigmaPower (248 : Fin 1536) ≤ ((20496368724747 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_249 : sigmaFactor (249 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-789403021 / 16097280 : ℚ) : ℝ) - Real.exp ((-1580211017 / 32194560 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_249 : sigmaPower (249 : Fin 1536) ≤ ((10241964801431 / 17592186044416 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_250 : sigmaFactor (250 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-2366249061 / 48283648 : ℚ) : ℝ) - Real.exp ((-1184178083 / 24141824 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_250 : sigmaPower (250 : Fin 1536) ≤ ((163771890080265 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_251 : sigmaFactor (251 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-1182144887 / 24137728 : ℚ) : ℝ) - Real.exp ((-4732793043 / 96550912 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_251 : sigmaPower (251 : Fin 1536) ≤ ((163672309552891 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_252 : sigmaFactor (252 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-393721867 / 8044544 : ℚ) : ℝ) - Real.exp ((-98518233 / 2011136 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_252 : sigmaPower (252 : Fin 1536) ≤ ((40893173805893 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_253 : sigmaFactor (253 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-2360373345 / 48259072 : ℚ) : ℝ) - Real.exp ((-4724958755 / 96518144 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_253 : sigmaPower (253 : Fin 1536) ≤ ((163473047075097 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_254 : sigmaFactor (254 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-2358416203 / 48250880 : ℚ) : ℝ) - Real.exp ((-1180260939 / 24125440 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_254 : sigmaPower (254 : Fin 1536) ≤ ((81686682545119 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_255 : sigmaFactor (255 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-3068307 / 62816 : ℚ) : ℝ) - Real.exp ((-1572376729 / 32161792 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_255 : sigmaPower (255 : Fin 1536) ≤ ((81636824625879 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

end LegendreK6.M2Pilot.Enclosures.Sigma001
