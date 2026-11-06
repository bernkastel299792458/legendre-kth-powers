import LegendreK6.M2PilotDefinitions
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp

/-! Generated proposals: every bound is checked by Lean, not by trusting Arb. -/
namespace LegendreK6.M2Pilot.Enclosures.Sigma009
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem sigma_factor_upper_1152 : sigmaFactor (1152 : Fin 1536) ≤ ((73985 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-4632881 / 212992 : ℚ) : ℝ) - Real.exp ((-36267 / 1664 : ℚ) : ℝ)) ≤ ((73985 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1152 : sigmaPower (1152 : Fin 1536) ≤ ((57738456761161 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1153 : sigmaFactor (1153 : Fin 1536) ≤ ((76069 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-888198795 / 40886272 : ℚ) : ℝ) - Real.exp ((-1779966155 / 81772544 : ℚ) : ℝ)) ≤ ((76069 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1153 : sigmaPower (1153 : Fin 1536) ≤ ((57599634585017 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1154 : sigmaFactor (1154 : Fin 1536) ≤ ((19553 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-886885153 / 40878080 : ℚ) : ℝ) - Real.exp ((-444334539 / 20439040 : ℚ) : ℝ)) ≤ ((19553 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1154 : sigmaPower (1154 : Fin 1536) ≤ ((28730378384361 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1155 : sigmaFactor (1155 : Fin 1536) ≤ ((80415 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-147595371 / 6811648 : ℚ) : ℝ) - Real.exp ((-591570529 / 27246592 : ℚ) : ℝ)) ≤ ((80415 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1155 : sigmaPower (1155 : Fin 1536) ≤ ((57321823278819 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1156 : sigmaFactor (1156 : Fin 1536) ≤ ((82679 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-442130007 / 20430848 : ℚ) : ℝ) - Real.exp ((-110755403 / 5107712 : ℚ) : ℝ)) ≤ ((82679 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1156 : sigmaPower (1156 : Fin 1536) ≤ ((57182834081823 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1157 : sigmaFactor (1157 : Fin 1536) ≤ ((85007 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-882948517 / 40853504 : ℚ) : ℝ) - Real.exp ((-1769462739 / 81707008 : ℚ) : ℝ)) ≤ ((85007 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1157 : sigmaPower (1157 : Fin 1536) ≤ ((57043789144223 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1158 : sigmaFactor (1158 : Fin 1536) ≤ ((10925 / 35184372088832 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-293879245 / 13615104 : ℚ) : ℝ) - Real.exp ((-147236705 / 6807552 : ℚ) : ℝ)) ≤ ((10925 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1158 : sigmaPower (1158 : Fin 1536) ≤ ((1778271513515 / 8796093022208 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1159 : sigmaFactor (1159 : Fin 1536) ≤ ((89859 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-220081917 / 10209280 : ℚ) : ℝ) - Real.exp ((-1764219611 / 81674240 : ℚ) : ℝ)) ≤ ((89859 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1159 : sigmaPower (1159 : Fin 1536) ≤ ((56765531913029 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1160 : sigmaFactor (1160 : Fin 1536) ≤ ((92387 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-219754579 / 10207232 : ℚ) : ℝ) - Real.exp ((-27525003 / 1275904 : ℚ) : ℝ)) ≤ ((92387 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1160 : sigmaPower (1160 : Fin 1536) ≤ ((28313159776139 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1161 : sigmaFactor (1161 : Fin 1536) ≤ ((94985 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-26597263 / 1236992 : ℚ) : ℝ) - Real.exp ((-53302491 / 2473984 : ℚ) : ℝ)) ≤ ((94985 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1161 : sigmaPower (1161 : Fin 1536) ≤ ((441305088411 / 2199023255552 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1162 : sigmaFactor (1162 : Fin 1536) ≤ ((12207 / 35184372088832 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-876401757 / 40812544 : ℚ) : ℝ) - Real.exp ((-439091411 / 20406272 : ℚ) : ℝ)) ≤ ((12207 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1162 : sigmaPower (1162 : Fin 1536) ≤ ((56347727172373 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1163 : sigmaFactor (1163 : Fin 1536) ≤ ((50201 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-25738075 / 1200128 : ℚ) : ℝ) - Real.exp ((-103161795 / 4800512 : ℚ) : ℝ)) ≤ ((50201 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1163 : sigmaPower (1163 : Fin 1536) ≤ ((14052086771475 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1164 : sigmaFactor (1164 : Fin 1536) ≤ ((103223 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-145631343 / 6799360 : ℚ) : ℝ) - Real.exp ((-36482017 / 1699840 : ℚ) : ℝ)) ≤ ((103223 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1164 : sigmaPower (1164 : Fin 1536) ≤ ((56068911023489 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1165 : sigmaFactor (1165 : Fin 1536) ≤ ((26531 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-872482281 / 40787968 : ℚ) : ℝ) - Real.exp ((-1748524547 / 81575936 : ℚ) : ℝ)) ≤ ((26531 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1165 : sigmaPower (1165 : Fin 1536) ≤ ((13982354737853 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1166 : sigmaFactor (1166 : Fin 1536) ≤ ((109105 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-871177219 / 40779776 : ℚ) : ℝ) - Real.exp ((-436478427 / 20389888 : ℚ) : ℝ)) ≤ ((109105 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1166 : sigmaPower (1166 : Fin 1536) ≤ ((55789870835915 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1167 : sigmaFactor (1167 : Fin 1536) ≤ ((56085 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-36244703 / 1698816 : ℚ) : ℝ) - Real.exp ((-581101433 / 27181056 : ℚ) : ℝ)) ≤ ((56085 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1167 : sigmaPower (1167 : Fin 1536) ≤ ((3478141665201 / 17592186044416 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1168 : sigmaFactor (1168 : Fin 1536) ≤ ((115319 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-108571155 / 5095424 : ℚ) : ℝ) - Real.exp ((-6799595 / 318464 : ℚ) : ℝ)) ≤ ((115319 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1168 : sigmaPower (1168 : Fin 1536) ≤ ((13877651584877 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1169 : sigmaFactor (1169 : Fin 1536) ≤ ((118557 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-867266323 / 40755200 : ℚ) : ℝ) - Real.exp ((-1738089771 / 81510400 : ℚ) : ℝ)) ≤ ((118557 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1169 : sigmaPower (1169 : Fin 1536) ≤ ((27685444945477 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1170 : sigmaFactor (1170 : Fin 1536) ≤ ((30471 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-288654707 / 13582336 : ℚ) : ℝ) - Real.exp ((-144623721 / 6791168 : ℚ) : ℝ)) ≤ ((30471 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1170 : sigmaPower (1170 : Fin 1536) ≤ ((13807779315923 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1171 : sigmaFactor (1171 : Fin 1536) ≤ ((15663 / 35184372088832 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-432331317 / 20369408 : ℚ) : ℝ) - Real.exp ((-1732880963 / 81477632 : ℚ) : ℝ)) ≤ ((15663 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1171 : sigmaPower (1171 : Fin 1536) ≤ ((27545644211915 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1172 : sigmaFactor (1172 : Fin 1536) ≤ ((32205 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-39243721 / 1851392 : ℚ) : ℝ) - Real.exp ((-9831129 / 462848 : ℚ) : ℝ)) ≤ ((32205 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1172 : sigmaPower (1172 : Fin 1536) ≤ ((13737850834363 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1173 : sigmaFactor (1173 : Fin 1536) ≤ ((8277 / 17592186044416 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-287353935 / 13574144 : ℚ) : ℝ) - Real.exp ((-575892625 / 27148288 : ℚ) : ℝ)) ≤ ((8277 / 17592186044416 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1173 : sigmaPower (1173 : Fin 1536) ≤ ((54811461970613 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1174 : sigmaFactor (1174 : Fin 1536) ≤ ((68073 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-860762463 / 40714240 : ℚ) : ℝ) - Real.exp ((-431269619 / 20357120 : ℚ) : ℝ)) ≤ ((68073 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1174 : sigmaPower (1174 : Fin 1536) ≤ ((54671464289341 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1175 : sigmaFactor (1175 : Fin 1536) ≤ ((139963 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-214865959 / 10176512 : ℚ) : ℝ) - Real.exp ((-1722480507 / 81412096 : ℚ) : ℝ)) ≤ ((139963 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1175 : sigmaPower (1175 : Fin 1536) ≤ ((54531410259635 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1176 : sigmaFactor (1176 : Fin 1536) ≤ ((143885 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-71513827 / 3391488 : ℚ) : ℝ) - Real.exp ((-8957729 / 423936 : ℚ) : ℝ)) ≤ ((143885 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1176 : sigmaPower (1176 : Fin 1536) ≤ ((27195649923735 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1177 : sigmaFactor (1177 : Fin 1536) ≤ ((147917 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-856868727 / 40689664 : ℚ) : ℝ) - Real.exp ((-1717288859 / 81379328 : ℚ) : ℝ)) ≤ ((147917 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1177 : sigmaPower (1177 : Fin 1536) ≤ ((54251133018791 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1178 : sigmaFactor (1178 : Fin 1536) ≤ ((152061 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-855572245 / 40681472 : ℚ) : ℝ) - Real.exp ((-428673795 / 20340736 : ℚ) : ℝ)) ≤ ((152061 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1178 : sigmaPower (1178 : Fin 1536) ≤ ((54110909739517 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1179 : sigmaFactor (1179 : Fin 1536) ≤ ((156319 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-142379413 / 6778880 : ℚ) : ℝ) - Real.exp ((-570700977 / 27115520 : ℚ) : ℝ)) ≤ ((156319 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1179 : sigmaPower (1179 : Fin 1536) ≤ ((26985314987769 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1180 : sigmaFactor (1180 : Fin 1536) ≤ ((20087 / 35184372088832 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-25087689 / 1196032 : ℚ) : ℝ) - Real.exp ((-6284971 / 299008 : ℚ) : ℝ)) ≤ ((20087 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1180 : sigmaPower (1180 : Fin 1536) ≤ ((26915146846359 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1181 : sigmaFactor (1181 : Fin 1536) ≤ ((165195 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-851687089 / 40656896 : ℚ) : ℝ) - Real.exp ((-1706922723 / 81313792 : ℚ) : ℝ)) ≤ ((165195 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1181 : sigmaPower (1181 : Fin 1536) ≤ ((13422475214223 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1182 : sigmaFactor (1182 : Fin 1536) ≤ ((84909 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-283464489 / 13549568 : ℚ) : ℝ) - Real.exp ((-142027897 / 6774784 : ℚ) : ℝ)) ≤ ((84909 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1182 : sigmaPower (1182 : Fin 1536) ≤ ((26774725716935 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1183 : sigmaFactor (1183 : Fin 1536) ≤ ((87285 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-438585 / 20992 : ℚ) : ℝ) - Real.exp ((-14064035 / 671744 : ℚ) : ℝ)) ≤ ((87285 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1183 : sigmaPower (1183 : Fin 1536) ≤ ((53408945389431 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1184 : sigmaFactor (1184 : Fin 1536) ≤ ((179453 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-52988023 / 2539520 : ℚ) : ℝ) - Real.exp ((-1659339 / 79360 : ℚ) : ℝ)) ≤ ((179453 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1184 : sigmaPower (1184 : Fin 1536) ≤ ((53268382689329 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1185 : sigmaFactor (1185 : Fin 1536) ≤ ((23059 / 35184372088832 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-282172297 / 13541376 : ℚ) : ℝ) - Real.exp ((-565526489 / 27082752 : ℚ) : ℝ)) ≤ ((23059 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1185 : sigmaPower (1185 : Fin 1536) ≤ ((53127763299289 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1186 : sigmaFactor (1186 : Fin 1536) ≤ ((94815 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-845226129 / 40615936 : ℚ) : ℝ) - Real.exp ((-423499307 / 20307968 : ℚ) : ℝ)) ≤ ((94815 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1186 : sigmaPower (1186 : Fin 1536) ≤ ((26493543592505 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1187 : sigmaFactor (1187 : Fin 1536) ≤ ((194931 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-421968041 / 20303872 : ℚ) : ℝ) - Real.exp ((-1691416419 / 81215488 : ℚ) : ℝ)) ≤ ((194931 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1187 : sigmaPower (1187 : Fin 1536) ≤ ((26423177156081 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1188 : sigmaFactor (1188 : Fin 1536) ≤ ((200379 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-140441125 / 6766592 : ℚ) : ℝ) - Real.exp ((-35184105 / 1691648 : ℚ) : ℝ)) ≤ ((200379 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1188 : sigmaPower (1188 : Fin 1536) ≤ ((26352782323193 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1189 : sigmaFactor (1189 : Fin 1536) ≤ ((205977 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-841358133 / 40591360 : ℚ) : ℝ) - Real.exp ((-1686259091 / 81182720 : ℚ) : ℝ)) ≤ ((205977 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1189 : sigmaPower (1189 : Fin 1536) ≤ ((52564718153299 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1190 : sigmaFactor (1190 : Fin 1536) ≤ ((211731 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-840070231 / 40583168 : ℚ) : ℝ) - Real.exp ((-420920643 / 20291584 : ℚ) : ℝ)) ≤ ((211731 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1190 : sigmaPower (1190 : Fin 1536) ≤ ((26211907399243 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1191 : sigmaFactor (1191 : Fin 1536) ≤ ((54411 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-69898587 / 3381248 : ℚ) : ℝ) - Real.exp ((-560369161 / 27049984 : ℚ) : ℝ)) ≤ ((54411 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1191 : sigmaPower (1191 : Fin 1536) ≤ ((13070713636877 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1192 : sigmaFactor (1192 : Fin 1536) ≤ ((223721 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-209374143 / 10141696 : ℚ) : ℝ) - Real.exp ((-26227091 / 1267712 : ℚ) : ℝ)) ≤ ((223721 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1192 : sigmaPower (1192 : Fin 1536) ≤ ((52141837365895 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1193 : sigmaFactor (1193 : Fin 1536) ≤ ((114983 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-836210815 / 40558592 : ℚ) : ℝ) - Real.exp ((-1675961595 / 81117184 : ℚ) : ℝ)) ≤ ((114983 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1193 : sigmaPower (1193 : Fin 1536) ≤ ((52000763219151 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1194 : sigmaFactor (1194 : Fin 1536) ≤ ((236383 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-25300781 / 1228800 : ℚ) : ℝ) - Real.exp ((-12677203 / 614400 : ℚ) : ℝ)) ≤ ((236383 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1194 : sigmaPower (1194 : Fin 1536) ≤ ((3241227004547 / 17592186044416 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1195 : sigmaFactor (1195 : Fin 1536) ≤ ((242979 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-416820723 / 20271104 : ℚ) : ℝ) - Real.exp ((-1670821427 / 81084416 : ℚ) : ℝ)) ≤ ((242979 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1195 : sigmaPower (1195 : Fin 1536) ≤ ((51718443892145 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1196 : sigmaFactor (1196 : Fin 1536) ≤ ((62439 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-416178917 / 20267008 : ℚ) : ℝ) - Real.exp ((-104265843 / 5066752 : ℚ) : ℝ)) ≤ ((62439 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1196 : sigmaPower (1196 : Fin 1536) ≤ ((51577198642751 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1197 : sigmaFactor (1197 : Fin 1536) ≤ ((256721 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-16295587 / 794624 : ℚ) : ℝ) - Real.exp ((-32660529 / 1589248 : ℚ) : ℝ)) ≤ ((256721 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1197 : sigmaPower (1197 : Fin 1536) ≤ ((51435896289961 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1198 : sigmaFactor (1198 : Fin 1536) ≤ ((263879 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-829792755 / 40517632 : ℚ) : ℝ) - Real.exp ((-415780475 / 20258816 : ℚ) : ℝ)) ≤ ((263879 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1198 : sigmaPower (1198 : Fin 1536) ≤ ((51294536799139 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1199 : sigmaFactor (1199 : Fin 1536) ≤ ((135617 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-103563911 / 5063680 : ℚ) : ℝ) - Real.exp ((-1660558251 / 81018880 : ℚ) : ℝ)) ≤ ((135617 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1199 : sigmaPower (1199 : Fin 1536) ≤ ((51153120135621 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1200 : sigmaFactor (1200 : Fin 1536) ≤ ((34849 / 35184372088832 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-34467939 / 1687552 : ℚ) : ℝ) - Real.exp ((-2158849 / 105472 : ℚ) : ℝ)) ≤ ((34849 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1200 : sigmaPower (1200 : Fin 1536) ≤ ((51011646264715 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1201 : sigmaFactor (1201 : Fin 1536) ≤ ((8955 / 8796093022208 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-825950499 / 40493056 : ℚ) : ℝ) - Real.exp ((-1655435243 / 80986112 : ℚ) : ℝ)) ≤ ((8955 / 8796093022208 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1201 : sigmaPower (1201 : Fin 1536) ≤ ((12717528787925 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1202 : sigmaFactor (1202 : Fin 1536) ≤ ((294541 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-824671177 / 40484864 : ℚ) : ℝ) - Real.exp ((-413218971 / 20242432 : ℚ) : ℝ)) ≤ ((294541 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1202 : sigmaPower (1202 : Fin 1536) ≤ ((50728526761829 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1203 : sigmaFactor (1203 : Fin 1536) ≤ ((302743 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-137232095 / 6746112 : ℚ) : ℝ) - Real.exp ((-550105985 / 26984448 : ℚ) : ℝ)) ≤ ((302743 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1203 : sigmaPower (1203 : Fin 1536) ≤ ((50586881060325 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1204 : sigmaFactor (1204 : Fin 1536) ≤ ((77793 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-411057339 / 20234240 : ℚ) : ℝ) - Real.exp ((-102985091 / 5058560 : ℚ) : ℝ)) ≤ ((77793 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1204 : sigmaPower (1204 : Fin 1536) ≤ ((50445178012383 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1205 : sigmaFactor (1205 : Fin 1536) ≤ ((319833 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-74621591 / 3678208 : ℚ) : ℝ) - Real.exp ((-149564217 / 7356416 : ℚ) : ℝ)) ≤ ((319833 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1205 : sigmaPower (1205 : Fin 1536) ≤ ((25151708791585 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1206 : sigmaFactor (1206 : Fin 1536) ≤ ((82183 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-273187013 / 13484032 : ℚ) : ℝ) - Real.exp ((-136887729 / 6742016 : ℚ) : ℝ)) ≤ ((82183 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1206 : sigmaPower (1206 : Fin 1536) ≤ ((50161599737825 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1207 : sigmaFactor (1207 : Fin 1536) ≤ ((168939 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-204571323 / 10110976 : ℚ) : ℝ) - Real.exp ((-1640100539 / 80887808 : ℚ) : ℝ)) ≤ ((168939 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1207 : sigmaPower (1207 : Fin 1536) ≤ ((50019724441459 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1208 : sigmaFactor (1208 : Fin 1536) ≤ ((347275 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-204252565 / 10108928 : ℚ) : ℝ) - Real.exp ((-25586715 / 1263616 : ℚ) : ℝ)) ≤ ((347275 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1208 : sigmaPower (1208 : Fin 1536) ≤ ((49877791659155 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1209 : sigmaFactor (1209 : Fin 1536) ≤ ((356931 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-271911981 / 13475840 : ℚ) : ℝ) - Real.exp ((-545000137 / 26951680 : ℚ) : ℝ)) ≤ ((356931 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1209 : sigmaPower (1209 : Fin 1536) ≤ ((24867900677983 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1210 : sigmaFactor (1210 : Fin 1536) ≤ ((183427 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-814462341 / 40419328 : ℚ) : ℝ) - Real.exp ((-408113123 / 20209664 : ℚ) : ℝ)) ≤ ((183427 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1210 : sigmaPower (1210 : Fin 1536) ≤ ((49593753496919 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1211 : sigmaFactor (1211 : Fin 1536) ≤ ((188525 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-406594727 / 20205568 : ℚ) : ℝ) - Real.exp ((-1629906003 / 80822272 : ℚ) : ℝ)) ≤ ((188525 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1211 : sigmaPower (1211 : Fin 1536) ≤ ((49451648047011 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1212 : sigmaFactor (1212 : Fin 1536) ≤ ((387527 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-135319547 / 6733824 : ℚ) : ℝ) - Real.exp ((-33903353 / 1683456 : ℚ) : ℝ)) ≤ ((387527 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1212 : sigmaPower (1212 : Fin 1536) ≤ ((24654742485605 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1213 : sigmaFactor (1213 : Fin 1536) ≤ ((99573 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-810645825 / 40394752 : ℚ) : ℝ) - Real.exp ((-1624817315 / 80789504 : ℚ) : ℝ)) ≤ ((99573 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1213 : sigmaPower (1213 : Fin 1536) ≤ ((24583632117229 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1214 : sigmaFactor (1214 : Fin 1536) ≤ ((409353 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-47610299 / 2375680 : ℚ) : ℝ) - Real.exp ((-23856987 / 1187840 : ℚ) : ℝ)) ≤ ((409353 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1214 : sigmaPower (1214 : Fin 1536) ≤ ((49024985801667 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1215 : sigmaFactor (1215 : Fin 1536) ≤ ((420719 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-8417761 / 420608 : ℚ) : ℝ) - Real.exp ((-539911449 / 26918912 : ℚ) : ℝ)) ≤ ((420719 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1215 : sigmaPower (1215 : Fin 1536) ≤ ((6110331204715 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1216 : sigmaFactor (1216 : Fin 1536) ≤ ((216199 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-2292147 / 114688 : ℚ) : ℝ) - Real.exp ((-35893 / 1792 : ℚ) : ℝ)) ≤ ((216199 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1216 : sigmaPower (1216 : Fin 1536) ≤ ((48740255707473 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1217 : sigmaFactor (1217 : Fin 1536) ≤ ((222199 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-805567147 / 40361984 : ℚ) : ℝ) - Real.exp ((-1614657099 / 80723968 : ℚ) : ℝ)) ≤ ((222199 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1217 : sigmaPower (1217 : Fin 1536) ≤ ((48597803975753 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1218 : sigmaFactor (1218 : Fin 1536) ≤ ((57091 / 35184372088832 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-268099755 / 13451264 : ℚ) : ℝ) - Real.exp ((-134343385 / 6725632 : ℚ) : ℝ)) ≤ ((57091 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1218 : sigmaPower (1218 : Fin 1536) ≤ ((48455294407357 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1219 : sigmaFactor (1219 : Fin 1536) ≤ ((469397 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-401516049 / 20172800 : ℚ) : ℝ) - Real.exp ((-1609585571 / 80691200 : ℚ) : ℝ)) ≤ ((469397 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1219 : sigmaPower (1219 : Fin 1536) ≤ ((48312726967055 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1220 : sigmaFactor (1220 : Fin 1536) ≤ ((241207 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-400882823 / 20168704 : ℚ) : ℝ) - Real.exp ((-100440747 / 5042176 : ℚ) : ℝ)) ≤ ((241207 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1220 : sigmaPower (1220 : Fin 1536) ≤ ((48170101619587 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1221 : sigmaFactor (1221 : Fin 1536) ≤ ((495789 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-266833303 / 13443072 : ℚ) : ℝ) - Real.exp ((-534839921 / 26886144 : ℚ) : ℝ)) ≤ ((495789 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1221 : sigmaPower (1221 : Fin 1536) ≤ ((12006854582417 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1222 : sigmaFactor (1222 : Fin 1536) ≤ ((127383 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-799234887 / 40321024 : ℚ) : ℝ) - Real.exp ((-400497251 / 20160512 : ℚ) : ℝ)) ≤ ((127383 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1222 : sigmaPower (1222 : Fin 1536) ≤ ((47884677061979 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1223 : sigmaFactor (1223 : Fin 1536) ≤ ((523651 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-199492645 / 10078208 : ℚ) : ℝ) - Real.exp ((-1599459675 / 80625664 : ℚ) : ℝ)) ≤ ((523651 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1223 : sigmaPower (1223 : Fin 1536) ≤ ((47741877781175 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1224 : sigmaFactor (1224 : Fin 1536) ≤ ((538159 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-66392249 / 3358720 : ℚ) : ℝ) - Real.exp ((-8317353 / 419840 : ℚ) : ℝ)) ≤ ((538159 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1224 : sigmaPower (1224 : Fin 1536) ≤ ((11899755112971 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1225 : sigmaFactor (1225 : Fin 1536) ≤ ((553065 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-795444111 / 40296448 : ℚ) : ℝ) - Real.exp ((-1594405307 / 80592896 : ℚ) : ℝ)) ≤ ((553065 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1225 : sigmaPower (1225 : Fin 1536) ≤ ((23728052519351 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1226 : sigmaFactor (1226 : Fin 1536) ≤ ((142095 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-794181949 / 40288256 : ℚ) : ℝ) - Real.exp ((-397970067 / 20144128 : ℚ) : ℝ)) ≤ ((142095 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1226 : sigmaPower (1226 : Fin 1536) ≤ ((47313131506197 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1227 : sigmaFactor (1227 : Fin 1536) ≤ ((584115 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-12013947 / 610304 : ℚ) : ℝ) - Real.exp ((-48162323 / 2441216 : ℚ) : ℝ)) ≤ ((584115 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1227 : sigmaPower (1227 : Fin 1536) ≤ ((47170099818911 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1228 : sigmaFactor (1228 : Fin 1536) ≤ ((600281 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-395829885 / 20135936 : ℚ) : ℝ) - Real.exp ((-99177155 / 5033984 : ℚ) : ℝ)) ≤ ((600281 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1228 : sigmaPower (1228 : Fin 1536) ≤ ((5878376242669 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1229 : sigmaFactor (1229 : Fin 1536) ≤ ((616891 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-790399753 / 40263680 : ℚ) : ℝ) - Real.exp ((-1584313731 / 80527360 : ℚ) : ℝ)) ≤ ((616891 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1229 : sigmaPower (1229 : Fin 1536) ≤ ((46883861838005 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1230 : sigmaFactor (1230 : Fin 1536) ≤ ((633957 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-263046817 / 13418496 : ℚ) : ℝ) - Real.exp ((-131816201 / 6709248 : ℚ) : ℝ)) ≤ ((633957 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1230 : sigmaPower (1230 : Fin 1536) ≤ ((46740655473321 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1231 : sigmaFactor (1231 : Fin 1536) ≤ ((325745 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-5793249 / 295936 : ℚ) : ℝ) - Real.exp ((-92898619 / 4734976 : ℚ) : ℝ)) ≤ ((325745 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1231 : sigmaPower (1231 : Fin 1536) ≤ ((46597390811725 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1232 : sigmaFactor (1232 : Fin 1536) ≤ ((10461 / 4398046511104 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-98327999 / 5029888 : ℚ) : ℝ) - Real.exp ((-6159219 / 314368 : ℚ) : ℝ)) ≤ ((10461 / 4398046511104 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1232 : sigmaPower (1232 : Fin 1536) ≤ ((46454067817611 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1233 : sigmaFactor (1233 : Fin 1536) ≤ ((688011 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-261788945 / 13410304 : ℚ) : ℝ) - Real.exp ((-524748345 / 26820608 : ℚ) : ℝ)) ≤ ((688011 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1233 : sigmaPower (1233 : Fin 1536) ≤ ((11577671613837 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1234 : sigmaFactor (1234 : Fin 1536) ≤ ((707025 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-784110393 / 40222720 : ℚ) : ℝ) - Real.exp ((-392932859 / 20111360 : ℚ) : ℝ)) ≤ ((707025 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1234 : sigmaPower (1234 : Fin 1536) ≤ ((23083623344635 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1235 : sigmaFactor (1235 : Fin 1536) ≤ ((22705 / 8796093022208 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-391427333 / 20107264 : ℚ) : ℝ) - Real.exp ((-1569219267 / 80429056 : ℚ) : ℝ)) ≤ ((22705 / 8796093022208 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1235 : sigmaPower (1235 : Fin 1536) ≤ ((5752968560461 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1236 : sigmaFactor (1236 : Fin 1536) ≤ ((746629 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-130266609 / 6701056 : ℚ) : ℝ) - Real.exp ((-32639761 / 1675264 : ℚ) : ℝ)) ≤ ((746629 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1236 : sigmaPower (1236 : Fin 1536) ≤ ((22940095901439 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1237 : sigmaFactor (1237 : Fin 1536) ≤ ((47953 / 17592186044416 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-780345357 / 40198144 : ℚ) : ℝ) - Real.exp ((-1564199219 / 80396288 : ℚ) : ℝ)) ≤ ((47953 / 17592186044416 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1237 : sigmaPower (1237 : Fin 1536) ≤ ((45736576611093 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1238 : sigmaFactor (1238 : Fin 1536) ≤ ((394215 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-70826525 / 3653632 : ℚ) : ℝ) - Real.exp ((-35492985 / 1826816 : ℚ) : ℝ)) ≤ ((394215 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1238 : sigmaPower (1238 : Fin 1536) ≤ ((45592902872551 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1239 : sigmaFactor (1239 : Fin 1536) ≤ ((810193 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-64819909 / 3348480 : ℚ) : ℝ) - Real.exp ((-519728297 / 26787840 : ℚ) : ℝ)) ≤ ((810193 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1239 : sigmaPower (1239 : Fin 1536) ≤ ((22724585275723 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1240 : sigmaFactor (1240 : Fin 1536) ≤ ((416275 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-194146689 / 10043392 : ℚ) : ℝ) - Real.exp ((-24323123 / 1255424 : ℚ) : ℝ)) ≤ ((416275 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1240 : sigmaPower (1240 : Fin 1536) ≤ ((45305379611939 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1241 : sigmaFactor (1241 : Fin 1536) ≤ ((427759 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-775335319 / 40165376 : ℚ) : ℝ) - Real.exp ((-1554176283 / 80330752 : ℚ) : ℝ)) ≤ ((427759 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1241 : sigmaPower (1241 : Fin 1536) ≤ ((45161530018163 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1242 : sigmaFactor (1242 : Fin 1536) ≤ ((879115 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-258028199 / 13385728 : ℚ) : ℝ) - Real.exp ((-129306177 / 6692864 : ℚ) : ℝ)) ≤ ((879115 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1242 : sigmaPower (1242 : Fin 1536) ≤ ((22508810867111 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1243 : sigmaFactor (1243 : Fin 1536) ≤ ((225839 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-386417295 / 20074496 : ℚ) : ℝ) - Real.exp ((-1549173395 / 80297984 : ℚ) : ℝ)) ≤ ((225839 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1243 : sigmaPower (1243 : Fin 1536) ≤ ((44873654724191 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1244 : sigmaFactor (1244 : Fin 1536) ≤ ((928259 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-385792649 / 20070400 : ℚ) : ℝ) - Real.exp ((-96667131 / 5017600 : ℚ) : ℝ)) ≤ ((928259 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1244 : sigmaPower (1244 : Fin 1536) ≤ ((11182407238029 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1245 : sigmaFactor (1245 : Fin 1536) ≤ ((476921 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-256778907 / 13377536 : ℚ) : ℝ) - Real.exp ((-514725409 / 26755072 : ℚ) : ℝ)) ≤ ((476921 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1245 : sigmaPower (1245 : Fin 1536) ≤ ((44585544382011 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1246 : sigmaFactor (1246 : Fin 1536) ≤ ((245031 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-769088859 / 40124416 : ℚ) : ℝ) - Real.exp ((-385419947 / 20062208 : ℚ) : ℝ)) ≤ ((245031 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1246 : sigmaPower (1246 : Fin 1536) ≤ ((5555175122233 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1247 : sigmaFactor (1247 : Fin 1536) ≤ ((1007123 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-47990107 / 2507264 : ℚ) : ℝ) - Real.exp ((-1539184779 / 80232448 : ℚ) : ℝ)) ≤ ((1007123 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1247 : sigmaPower (1247 : Fin 1536) ≤ ((44297198703631 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1248 : sigmaFactor (1248 : Fin 1536) ≤ ((1034859 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-939455 / 49152 : ℚ) : ℝ) - Real.exp ((-29425 / 1536 : ℚ) : ℝ)) ≤ ((1034859 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1248 : sigmaPower (1248 : Fin 1536) ≤ ((44152937523241 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1249 : sigmaFactor (1249 : Fin 1536) ≤ ((132919 / 35184372088832 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-69577233 / 3645440 : ℚ) : ℝ) - Real.exp ((-139472641 / 7290880 : ℚ) : ℝ)) ≤ ((132919 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1249 : sigmaPower (1249 : Fin 1536) ≤ ((44008617400591 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1250 : sigmaFactor (1250 : Fin 1536) ≤ ((546311 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-764104561 / 40091648 : ℚ) : ℝ) - Real.exp ((-382927083 / 20045824 : ℚ) : ℝ)) ≤ ((546311 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1250 : sigmaPower (1250 : Fin 1536) ≤ ((21932119149775 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1251 : sigmaFactor (1251 : Fin 1536) ≤ ((561345 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-127143379 / 6680576 : ℚ) : ℝ) - Real.exp ((-509739681 / 26722304 : ℚ) : ℝ)) ≤ ((561345 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1251 : sigmaPower (1251 : Fin 1536) ≤ ((43719800183957 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1252 : sigmaFactor (1252 : Fin 1536) ≤ ((576789 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-380808351 / 20037632 : ℚ) : ℝ) - Real.exp ((-95420699 / 5009408 : ℚ) : ℝ)) ≤ ((576789 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1252 : sigmaPower (1252 : Fin 1536) ≤ ((21787651508811 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1253 : sigmaFactor (1253 : Fin 1536) ≤ ((1185307 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-760373845 / 40067072 : ℚ) : ℝ) - Real.exp ((-1524244755 / 80134144 : ℚ) : ℝ)) ≤ ((1185307 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1253 : sigmaPower (1253 : Fin 1536) ≤ ((10857686691081 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1254 : sigmaFactor (1254 : Fin 1536) ≤ ((1217901 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-253043901 / 13352960 : ℚ) : ℝ) - Real.exp ((-126813313 / 6676480 : ℚ) : ℝ)) ≤ ((1217901 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1254 : sigmaPower (1254 : Fin 1536) ≤ ((43286131387815 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1255 : sigmaFactor (1255 : Fin 1536) ≤ ((1251383 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-189472569 / 10012672 : ℚ) : ℝ) - Real.exp ((-1519276187 / 80101376 : ℚ) : ℝ)) ≤ ((1251383 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1255 : sigmaPower (1255 : Fin 1536) ≤ ((21570728425907 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1256 : sigmaFactor (1256 : Fin 1536) ≤ ((80361 / 17592186044416 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-189162391 / 10010624 : ℚ) : ℝ) - Real.exp ((-23699907 / 1251328 : ℚ) : ℝ)) ≤ ((80361 / 17592186044416 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1256 : sigmaPower (1256 : Fin 1536) ≤ ((42996723120013 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1257 : sigmaFactor (1257 : Fin 1536) ≤ ((660553 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-251803189 / 13344768 : ℚ) : ℝ) - Real.exp ((-504771113 / 26689536 : ℚ) : ℝ)) ≤ ((660553 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1257 : sigmaPower (1257 : Fin 1536) ≤ ((42851930156073 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1258 : sigmaFactor (1258 : Fin 1536) ≤ ((678699 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-754170285 / 40026112 : ℚ) : ℝ) - Real.exp ((-377958515 / 20013056 : ℚ) : ℝ)) ≤ ((678699 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1258 : sigmaPower (1258 : Fin 1536) ≤ ((21353538961813 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1259 : sigmaFactor (1259 : Fin 1536) ≤ ((348669 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-376465859 / 20008960 : ℚ) : ℝ) - Real.exp ((-1509356211 / 80035840 : ℚ) : ℝ)) ≤ ((348669 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1259 : sigmaPower (1259 : Fin 1536) ≤ ((1330067699571 / 8796093022208 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1260 : sigmaFactor (1260 : Fin 1536) ≤ ((716485 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-11389301 / 606208 : ℚ) : ℝ) - Real.exp ((-2853939 / 151552 : ℚ) : ℝ)) ≤ ((716485 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1260 : sigmaPower (1260 : Fin 1536) ≤ ((42417195507585 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1261 : sigmaFactor (1261 : Fin 1536) ≤ ((92019 / 17592186044416 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-750456729 / 40001536 : ℚ) : ℝ) - Real.exp ((-1504404803 / 80003072 : ℚ) : ℝ)) ≤ ((92019 / 17592186044416 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1261 : sigmaPower (1261 : Fin 1536) ≤ ((21136082625553 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1262 : sigmaFactor (1262 : Fin 1536) ≤ ((378177 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-749220307 / 39993344 : ℚ) : ℝ) - Real.exp ((-375482811 / 19996672 : ℚ) : ℝ)) ≤ ((378177 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1262 : sigmaPower (1262 : Fin 1536) ≤ ((42127075580347 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1263 : sigmaFactor (1263 : Fin 1536) ≤ ((777105 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-31166025 / 1666048 : ℚ) : ℝ) - Real.exp ((-499819705 / 26656768 : ℚ) : ℝ)) ≤ ((777105 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1263 : sigmaPower (1263 : Fin 1536) ≤ ((41981926458791 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1264 : sigmaFactor (1264 : Fin 1536) ≤ ((199605 / 35184372088832 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-93343701 / 4997120 : ℚ) : ℝ) - Real.exp ((-5847611 / 312320 : ℚ) : ℝ)) ≤ ((199605 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1264 : sigmaPower (1264 : Fin 1536) ≤ ((20918358924945 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1265 : sigmaFactor (1265 : Fin 1536) ≤ ((410157 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-43853843 / 2351104 : ℚ) : ℝ) - Real.exp ((-87912891 / 4702208 : ℚ) : ℝ)) ≤ ((410157 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1265 : sigmaPower (1265 : Fin 1536) ≤ ((41691449717067 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1266 : sigmaFactor (1266 : Fin 1536) ≤ ((842803 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-248093923 / 13320192 : ℚ) : ℝ) - Real.exp ((-124337609 / 6660096 : ℚ) : ℝ)) ≤ ((842803 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1266 : sigmaPower (1266 : Fin 1536) ≤ ((20773061011857 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1267 : sigmaFactor (1267 : Fin 1536) ≤ ((432951 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-371524461 / 19976192 : ℚ) : ℝ) - Real.exp ((-1489584899 / 79904768 : ℚ) : ℝ)) ≤ ((432951 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1267 : sigmaPower (1267 : Fin 1536) ≤ ((5175091841649 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1268 : sigmaFactor (1268 : Fin 1536) ≤ ((1779257 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-370908395 / 19972096 : ℚ) : ℝ) - Real.exp ((-92944995 / 4993024 : ℚ) : ℝ)) ≤ ((1779257 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1268 : sigmaPower (1268 : Fin 1536) ≤ ((10313821952209 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1269 : sigmaFactor (1269 : Fin 1536) ≤ ((1827997 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-246861791 / 13312000 : ℚ) : ℝ) - Real.exp ((-494885457 / 26624000 : ℚ) : ℝ)) ≤ ((1827997 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1269 : sigmaPower (1269 : Fin 1536) ≤ ((41109781213947 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1270 : sigmaFactor (1270 : Fin 1536) ≤ ((469515 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-739354671 / 39927808 : ℚ) : ℝ) - Real.exp ((-370548563 / 19963904 : ℚ) : ℝ)) ≤ ((469515 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1270 : sigmaPower (1270 : Fin 1536) ≤ ((10241053727949 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1271 : sigmaFactor (1271 : Fin 1536) ≤ ((1929481 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-16775561 / 907264 : ℚ) : ℝ) - Real.exp ((-134521233 / 7258112 : ℚ) : ℝ)) ≤ ((1929481 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1271 : sigmaPower (1271 : Fin 1536) ≤ ((40818588865627 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1272 : sigmaFactor (1272 : Fin 1536) ≤ ((247787 / 35184372088832 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-61407951 / 3325952 : ℚ) : ℝ) - Real.exp ((-7694137 / 415744 : ℚ) : ℝ)) ≤ ((247787 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1272 : sigmaPower (1272 : Fin 1536) ≤ ((20336451519325 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1273 : sigmaFactor (1273 : Fin 1536) ≤ ((2036543 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-735666855 / 39903232 : ℚ) : ℝ) - Real.exp ((-1474816475 / 79806464 : ℚ) : ℝ)) ≤ ((2036543 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1273 : sigmaPower (1273 : Fin 1536) ≤ ((316618417141 / 2199023255552 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1274 : sigmaFactor (1274 : Fin 1536) ≤ ((523065 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-734439013 / 39895040 : ℚ) : ℝ) - Real.exp ((-368090019 / 19947520 : ℚ) : ℝ)) ≤ ((523065 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1274 : sigmaPower (1274 : Fin 1536) ≤ ((10095337973743 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1275 : sigmaFactor (1275 : Fin 1536) ≤ ((2149487 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-122201981 / 6647808 : ℚ) : ℝ) - Real.exp ((-489968369 / 26591232 : ℚ) : ℝ)) ≤ ((2149487 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1275 : sigmaPower (1275 : Fin 1536) ≤ ((40235486504543 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1276 : sigmaFactor (1276 : Fin 1536) ≤ ((276033 / 35184372088832 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-365992737 / 19939328 : ℚ) : ℝ) - Real.exp ((-91715723 / 4984832 : ℚ) : ℝ)) ≤ ((276033 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1276 : sigmaPower (1276 : Fin 1536) ≤ ((40089561185851 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1277 : sigmaFactor (1277 : Fin 1536) ≤ ((2268633 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-730759777 / 39870464 : ℚ) : ℝ) - Real.exp ((-1464999459 / 79740928 : ℚ) : ℝ)) ≤ ((2268633 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1277 : sigmaPower (1277 : Fin 1536) ≤ ((19971787950979 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1278 : sigmaFactor (1278 : Fin 1536) ≤ ((582659 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-243178265 / 13287424 : ℚ) : ℝ) - Real.exp ((-121879065 / 6643712 : ℚ) : ℝ)) ≤ ((582659 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1278 : sigmaPower (1278 : Fin 1536) ≤ ((39797530615893 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1279 : sigmaFactor (1279 : Fin 1536) ≤ ((2394317 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1721 / 100 : ℚ) : ℝ) * (Real.exp ((-2844963 / 155680 : ℚ) : ℝ) - Real.exp ((-1460099531 / 79708160 : ℚ) : ℝ)) ≤ ((2394317 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1279 : sigmaPower (1279 : Fin 1536) ≤ ((39651425290655 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

end LegendreK6.M2Pilot.Enclosures.Sigma009
