import LegendreK6.M2PilotDefinitions
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp

/-! Generated proposals: every bound is checked by Lean, not by trusting Arb. -/
namespace LegendreK6.M2Pilot.Enclosures.Sigma002
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem sigma_factor_upper_256 : sigmaFactor (256 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-18394563 / 376832 : ℚ) : ℝ) - Real.exp ((-35959 / 736 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_256 : sigmaPower (256 : Fin 1536) ≤ ((81586949771205 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_257 : sigmaFactor (257 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-2352549067 / 48226304 : ℚ) : ℝ) - Real.exp ((-4709307339 / 96452608 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_257 : sigmaPower (257 : Fin 1536) ≤ ((40768528986233 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_258 : sigmaFactor (258 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-783531595 / 16072704 : ℚ) : ℝ) - Real.exp ((-392116505 / 8036352 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_258 : sigmaPower (258 : Fin 1536) ≤ ((40743574610513 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_259 : sigmaFactor (259 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-106756419 / 2191360 : ℚ) : ℝ) - Real.exp ((-427408201 / 8765440 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_259 : sigmaPower (259 : Fin 1536) ≤ ((162874447016487 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_260 : sigmaFactor (260 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-1173344183 / 24100864 : ℚ) : ℝ) - Real.exp ((-293598987 / 6025216 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_260 : sigmaPower (260 : Fin 1536) ≤ ((40693640412735 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_261 : sigmaFactor (261 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-781578743 / 16064512 : ℚ) : ℝ) - Real.exp ((-1564559601 / 32129024 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_261 : sigmaPower (261 : Fin 1536) ≤ ((20334330291013 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_262 : sigmaFactor (262 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-137810871 / 2834432 : ℚ) : ℝ) - Real.exp ((-68967283 / 1417216 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_262 : sigmaPower (262 : Fin 1536) ≤ ((162574689030659 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_263 : sigmaFactor (263 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-585208525 / 12044288 : ℚ) : ℝ) - Real.exp ((-4685873115 / 96354304 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_263 : sigmaPower (263 : Fin 1536) ≤ ((40618675435319 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_264 : sigmaFactor (264 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-194907009 / 4014080 : ℚ) : ℝ) - Real.exp ((-24385273 / 501760 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_264 : sigmaPower (264 : Fin 1536) ≤ ((81187340221305 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_265 : sigmaFactor (265 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-2336934831 / 48160768 : ℚ) : ℝ) - Real.exp ((-4678073147 / 96321536 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_265 : sigmaPower (265 : Fin 1536) ≤ ((40568656279327 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_266 : sigmaFactor (266 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-2334986269 / 48152576 : ℚ) : ℝ) - Real.exp ((-1168543827 / 24076288 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_266 : sigmaPower (266 : Fin 1536) ≤ ((81087267874001 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_267 : sigmaFactor (267 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-388839737 / 8024064 : ℚ) : ℝ) - Real.exp ((-1556759633 / 32096256 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_267 : sigmaPower (267 : Fin 1536) ≤ ((162074412317315 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_268 : sigmaFactor (268 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-1165545645 / 24068096 : ℚ) : ℝ) - Real.exp ((-291648995 / 6017024 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_268 : sigmaPower (268 : Fin 1536) ≤ ((161974254807857 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_269 : sigmaFactor (269 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-2329144873 / 48128000 : ℚ) : ℝ) - Real.exp ((-4662490371 / 96256000 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_269 : sigmaPower (269 : Fin 1536) ≤ ((161874063202225 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_270 : sigmaFactor (270 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-70521187 / 1458176 : ℚ) : ℝ) - Real.exp ((-35292411 / 729088 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_270 : sigmaPower (270 : Fin 1536) ≤ ((80886918741503 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_271 : sigmaFactor (271 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-290656773 / 6013952 : ℚ) : ℝ) - Real.exp ((-4654707563 / 96223232 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_271 : sigmaPower (271 : Fin 1536) ≤ ((80836788816387 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_272 : sigmaFactor (272 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-290413739 / 6012928 : ℚ) : ℝ) - Real.exp ((-18167259 / 375808 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_272 : sigmaPower (272 : Fin 1536) ≤ ((40393320908523 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_273 : sigmaFactor (273 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-773788785 / 16031744 : ℚ) : ℝ) - Real.exp ((-1548976825 / 32063488 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_273 : sigmaPower (273 : Fin 1536) ≤ ((80736477734755 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_274 : sigmaFactor (274 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-2319423513 / 48087040 : ℚ) : ℝ) - Real.exp ((-1160761019 / 24043520 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_274 : sigmaPower (274 : Fin 1536) ≤ ((161372593121567 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_275 : sigmaFactor (275 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-1158740693 / 24039424 : ℚ) : ℝ) - Real.exp ((-4639159107 / 96157696 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_275 : sigmaPower (275 : Fin 1536) ≤ ((80636098286395 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_276 : sigmaFactor (276 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-385923329 / 8011776 : ℚ) : ℝ) - Real.exp ((-96568241 / 2002944 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_276 : sigmaPower (276 : Fin 1536) ≤ ((161171765805693 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_277 : sigmaFactor (277 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-2313599277 / 48062464 : ℚ) : ℝ) - Real.exp ((-4631393459 / 96124928 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_277 : sigmaPower (277 : Fin 1536) ≤ ((40267825200695 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_278 : sigmaFactor (278 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-2311659295 / 48054272 : ℚ) : ℝ) - Real.exp ((-1156878195 / 24027136 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_278 : sigmaPower (278 : Fin 1536) ≤ ((80485400773271 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_279 : sigmaFactor (279 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-11322157 / 235520 : ℚ) : ℝ) - Real.exp ((-90659481 / 1884160 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_279 : sigmaPower (279 : Fin 1536) ≤ ((80435134009729 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_280 : sigmaFactor (280 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-576945369 / 12009472 : ℚ) : ℝ) - Real.exp ((-72183683 / 1501184 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_280 : sigmaPower (280 : Fin 1536) ≤ ((160769700203995 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_281 : sigmaFactor (281 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-209622149 / 4366336 : ℚ) : ℝ) - Real.exp ((-419625393 / 8732672 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_281 : sigmaPower (281 : Fin 1536) ≤ ((10041818630163 / 17592186044416 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_282 : sigmaFactor (282 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-767968839 / 16007168 : ℚ) : ℝ) - Real.exp ((-384333697 / 8003584 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_282 : sigmaPower (282 : Fin 1536) ≤ ((160568461637741 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_283 : sigmaFactor (283 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-1150985055 / 24006656 : ℚ) : ℝ) - Real.exp ((-4608130835 / 96026624 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_283 : sigmaPower (283 : Fin 1536) ≤ ((10029236928239 / 17592186044416 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_284 : sigmaFactor (284 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-1150017209 / 24002560 : ℚ) : ℝ) - Real.exp ((-287766171 / 6000640 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_284 : sigmaPower (284 : Fin 1536) ≤ ((80183542853639 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_285 : sigmaFactor (285 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-766033147 / 15998976 : ℚ) : ℝ) - Real.exp ((-1533462689 / 31997952 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_285 : sigmaPower (285 : Fin 1536) ≤ ((40066586546627 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_286 : sigmaFactor (286 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-2296165179 / 47988736 : ℚ) : ℝ) - Real.exp ((-1149129707 / 23994368 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_286 : sigmaPower (286 : Fin 1536) ≤ ((160165572271911 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_287 : sigmaFactor (287 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-143389477 / 2998784 : ℚ) : ℝ) - Real.exp ((-4592651019 / 95961088 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_287 : sigmaPower (287 : Fin 1536) ≤ ((80032381972935 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_288 : sigmaFactor (288 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-47756225 / 999424 : ℚ) : ℝ) - Real.exp ((-1493745 / 31232 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_288 : sigmaPower (288 : Fin 1536) ≤ ((39990980297689 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_289 : sigmaFactor (289 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-2290366683 / 47964160 : ℚ) : ℝ) - Real.exp ((-4584919691 / 95928320 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_289 : sigmaPower (289 : Fin 1536) ≤ ((2497860062327 / 4398046511104 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_290 : sigmaFactor (290 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-2288435281 / 47955968 : ℚ) : ℝ) - Real.exp ((-1145264043 / 23977984 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_290 : sigmaPower (290 : Fin 1536) ≤ ((39940533080683 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_291 : sigmaFactor (291 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-381084099 / 7991296 : ℚ) : ℝ) - Real.exp ((-1525731361 / 31965184 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_291 : sigmaPower (291 : Fin 1536) ≤ ((79830593087253 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_292 : sigmaFactor (292 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-103844301 / 2179072 : ℚ) : ℝ) - Real.exp ((-25984849 / 544768 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_292 : sigmaPower (292 : Fin 1536) ≤ ((79780102763285 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_293 : sigmaFactor (293 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-2282645365 / 47931392 : ℚ) : ℝ) - Real.exp ((-4569474195 / 95862784 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_293 : sigmaPower (293 : Fin 1536) ≤ ((39864797590309 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_294 : sigmaFactor (294 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-760238941 / 15974400 : ℚ) : ℝ) - Real.exp ((-380468033 / 7987200 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_294 : sigmaPower (294 : Fin 1536) ≤ ((159358140660803 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_295 : sigmaFactor (295 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-569697249 / 11978752 : ℚ) : ℝ) - Real.exp ((-4561760027 / 95830016 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_295 : sigmaPower (295 : Fin 1536) ≤ ((159257056407557 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_296 : sigmaFactor (296 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-33483263 / 704512 : ℚ) : ℝ) - Real.exp ((-4189251 / 88064 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_296 : sigmaPower (296 : Fin 1536) ≤ ((159155937583773 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_297 : sigmaFactor (297 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-758311829 / 15966208 : ℚ) : ℝ) - Real.exp ((-1518017193 / 31932416 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_297 : sigmaPower (297 : Fin 1536) ≤ ((79527392085857 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_298 : sigmaFactor (298 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-2273009805 / 47890432 : ℚ) : ℝ) - Real.exp ((-1137549875 / 23945216 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_298 : sigmaPower (298 : Fin 1536) ≤ ((158953596153629 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_299 : sigmaFactor (299 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-1135542419 / 23941120 : ℚ) : ℝ) - Real.exp ((-4546348851 / 95764480 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_299 : sigmaPower (299 : Fin 1536) ≤ ((158852373511757 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_300 : sigmaFactor (300 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-378193431 / 7979008 : ℚ) : ℝ) - Real.exp ((-94635409 / 1994752 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_300 : sigmaPower (300 : Fin 1536) ≤ ((39687779057081 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_301 : sigmaFactor (301 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-2267237049 / 47865856 : ℚ) : ℝ) - Real.exp ((-4538651843 / 95731712 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_301 : sigmaPower (301 : Fin 1536) ≤ ((158649824285543 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_302 : sigmaFactor (302 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-2265314227 / 47857664 : ℚ) : ℝ) - Real.exp ((-1133701371 / 23928832 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_302 : sigmaPower (302 : Fin 1536) ≤ ((158548497665617 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_303 : sigmaFactor (303 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-8573455 / 181248 : ℚ) : ℝ) - Real.exp ((-137301835 / 2899968 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_303 : sigmaPower (303 : Fin 1536) ≤ ((79223568175367 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_304 : sigmaFactor (304 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-282683841 / 5980160 : ℚ) : ℝ) - Real.exp ((-17684051 / 373760 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_304 : sigmaPower (304 : Fin 1536) ≤ ((158345740323073 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_305 : sigmaFactor (305 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-2259550051 / 47833088 : ℚ) : ℝ) - Real.exp ((-4523274987 / 95666176 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_305 : sigmaPower (305 : Fin 1536) ≤ ((158244309564797 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_306 : sigmaFactor (306 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-752543363 / 15941632 : ℚ) : ℝ) - Real.exp ((-376619529 / 7970816 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_306 : sigmaPower (306 : Fin 1536) ≤ ((39535711014515 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_307 : sigmaFactor (307 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-1127855421 / 23908352 : ℚ) : ℝ) - Real.exp ((-4515595139 / 95633408 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_307 : sigmaPower (307 : Fin 1536) ≤ ((79020671892501 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_308 : sigmaFactor (308 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-1126896155 / 23904256 : ℚ) : ℝ) - Real.exp ((-281984835 / 5976064 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_308 : sigmaPower (308 : Fin 1536) ≤ ((157939808727753 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_309 : sigmaFactor (309 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-750624831 / 15933440 : ℚ) : ℝ) - Real.exp ((-1502640337 / 31866880 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_309 : sigmaPower (309 : Fin 1536) ≤ ((157838238868427 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_310 : sigmaFactor (310 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-2249957391 / 47792128 : ℚ) : ℝ) - Real.exp ((-1126021523 / 23896064 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_310 : sigmaPower (310 : Fin 1536) ≤ ((19717079273641 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_311 : sigmaFactor (311 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-562010251 / 11945984 : ℚ) : ℝ) - Real.exp ((-4500252603 / 95567872 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_311 : sigmaPower (311 : Fin 1536) ≤ ((157634994671949 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_312 : sigmaFactor (312 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-187177111 / 3981312 : ℚ) : ℝ) - Real.exp ((-23418857 / 497664 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_312 : sigmaPower (312 : Fin 1536) ≤ ((19691665037371 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_313 : sigmaFactor (313 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-132012375 / 2809856 : ℚ) : ℝ) - Real.exp ((-264269995 / 5619712 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_313 : sigmaPower (313 : Fin 1536) ≤ ((157431611052253 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_314 : sigmaFactor (314 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-203845103 / 4341760 : ℚ) : ℝ) - Real.exp ((-102017289 / 2170880 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_314 : sigmaPower (314 : Fin 1536) ≤ ((78664933456929 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_315 : sigmaFactor (315 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-373397101 / 7958528 : ℚ) : ℝ) - Real.exp ((-1494977649 / 31834112 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_315 : sigmaPower (315 : Fin 1536) ≤ ((78614043932913 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_316 : sigmaFactor (316 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-1119234897 / 23871488 : ℚ) : ℝ) - Real.exp ((-280069163 / 5967872 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_316 : sigmaPower (316 : Fin 1536) ≤ ((78563136945093 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_317 : sigmaFactor (317 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-2236557697 / 47734784 : ℚ) : ℝ) - Real.exp ((-4477281699 / 95469568 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_317 : sigmaPower (317 : Fin 1536) ≤ ((39256106242239 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_318 : sigmaFactor (318 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-744882105 / 15908864 : ℚ) : ℝ) - Real.exp ((-372788185 / 7954432 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_318 : sigmaPower (318 : Fin 1536) ≤ ((78461270542071 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_319 : sigmaFactor (319 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-69772989 / 1491200 : ℚ) : ℝ) - Real.exp ((-4469636171 / 95436800 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_319 : sigmaPower (319 : Fin 1536) ≤ ((156820622217737 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_320 : sigmaFactor (320 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-69713303 / 1490944 : ℚ) : ℝ) - Real.exp ((-1090287 / 23296 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_320 : sigmaPower (320 : Fin 1536) ≤ ((156718668351721 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_321 : sigmaFactor (321 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-742972153 / 15900672 : ℚ) : ℝ) - Real.exp ((-1487332121 / 31801344 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_321 : sigmaPower (321 : Fin 1536) ≤ ((156616679468063 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_322 : sigmaFactor (322 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-2227007937 / 47693824 : ℚ) : ℝ) - Real.exp ((-1114544651 / 23846912 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_322 : sigmaPower (322 : Fin 1536) ≤ ((156514655548717 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_323 : sigmaFactor (323 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-1112550065 / 23842816 : ℚ) : ℝ) - Real.exp ((-4454362275 / 95371264 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_323 : sigmaPower (323 : Fin 1536) ≤ ((156412596575629 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_324 : sigmaFactor (324 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-370532173 / 7946240 : ℚ) : ℝ) - Real.exp ((-92719737 / 1986560 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_324 : sigmaPower (324 : Fin 1536) ≤ ((156310502530729 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_325 : sigmaFactor (325 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-201935151 / 4333568 : ℚ) : ℝ) - Real.exp ((-404248537 / 8667136 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_325 : sigmaPower (325 : Fin 1536) ≤ ((156208373395935 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_326 : sigmaFactor (326 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-2219380999 / 47661056 : ℚ) : ℝ) - Real.exp ((-1110730467 / 23830528 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_326 : sigmaPower (326 : Fin 1536) ≤ ((156106209153155 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_327 : sigmaFactor (327 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-184789671 / 3971072 : ℚ) : ℝ) - Real.exp ((-1479703753 / 31768576 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_327 : sigmaPower (327 : Fin 1536) ≤ ((19500501223035 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_328 : sigmaFactor (328 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-553892955 / 11911168 : ℚ) : ℝ) - Real.exp ((-69301595 / 1488896 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_328 : sigmaPower (328 : Fin 1536) ≤ ((77950887635597 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_329 : sigmaFactor (329 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-2213668303 / 47636480 : ℚ) : ℝ) - Real.exp ((-4431494331 / 95272960 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_329 : sigmaPower (329 : Fin 1536) ≤ ((38949876398941 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_330 : sigmaFactor (330 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-43367951 / 933888 : ℚ) : ℝ) - Real.exp ((-21704353 / 466944 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_330 : sigmaPower (330 : Fin 1536) ≤ ((155697200739847 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_331 : sigmaFactor (331 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-1104931707 / 23810048 : ℚ) : ℝ) - Real.exp ((-4423883123 / 95240192 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_331 : sigmaPower (331 : Fin 1536) ≤ ((19449357585661 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_332 : sigmaFactor (332 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-1103981021 / 23805952 : ℚ) : ℝ) - Real.exp ((-276254979 / 5951488 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_332 : sigmaPower (332 : Fin 1536) ≤ ((38873121353479 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_333 : sigmaFactor (333 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-735353795 / 15867904 : ℚ) : ℝ) - Real.exp ((-1472092545 / 31735808 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_333 : sigmaPower (333 : Fin 1536) ≤ ((4855939840861 / 8796093022208 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_334 : sigmaFactor (334 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-2204161443 / 47595520 : ℚ) : ℝ) - Real.exp ((-1103119259 / 23797760 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_334 : sigmaPower (334 : Fin 1536) ≤ ((77643814574001 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_335 : sigmaFactor (335 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-275282777 / 5948416 : ℚ) : ℝ) - Real.exp ((-4408677867 / 95174656 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_335 : sigmaPower (335 : Fin 1536) ≤ ((155185148117059 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_336 : sigmaFactor (336 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-757701 / 16384 : ℚ) : ℝ) - Real.exp ((-47401 / 1024 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_336 : sigmaPower (336 : Fin 1536) ≤ ((155082631796505 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_337 : sigmaFactor (337 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-2198465907 / 47570944 : ℚ) : ℝ) - Real.exp ((-4401083819 / 95141888 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_337 : sigmaPower (337 : Fin 1536) ≤ ((154980080168109 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_338 : sigmaFactor (338 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-2196568825 / 47562752 : ℚ) : ℝ) - Real.exp ((-1099322235 / 23781376 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_338 : sigmaPower (338 : Fin 1536) ≤ ((77438746606813 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_339 : sigmaFactor (339 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-365778743 / 7925760 : ℚ) : ℝ) - Real.exp ((-1464498497 / 31703040 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_339 : sigmaPower (339 : Fin 1536) ≤ ((9673429432175 / 17592186044416 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_340 : sigmaFactor (340 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-1096388403 / 23773184 : ℚ) : ℝ) - Real.exp ((-274356467 / 5943296 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_340 : sigmaPower (340 : Fin 1536) ≤ ((38668053313341 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_341 : sigmaFactor (341 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-2190881869 / 47538176 : ℚ) : ℝ) - Real.exp ((-4385912883 / 95076352 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_341 : sigmaPower (341 : Fin 1536) ≤ ((154569520211033 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_342 : sigmaFactor (342 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-729662549 / 15843328 : ℚ) : ℝ) - Real.exp ((-365176977 / 7921664 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_342 : sigmaPower (342 : Fin 1536) ≤ ((38616697942379 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_343 : sigmaFactor (343 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-546773535 / 11880448 : ℚ) : ℝ) - Real.exp ((-4378335995 / 95043584 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_343 : sigmaPower (343 : Fin 1536) ≤ ((19295503488813 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_344 : sigmaFactor (344 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-546300337 / 11878400 : ℚ) : ℝ) - Real.exp ((-68352339 / 1484800 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_344 : sigmaPower (344 : Fin 1536) ≤ ((75322865535 / 137438953472 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_345 : sigmaFactor (345 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-727769757 / 15835136 : ℚ) : ℝ) - Real.exp ((-1456921609 / 31670272 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_345 : sigmaPower (345 : Fin 1536) ≤ ((154158393866709 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_346 : sigmaFactor (346 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-2181417909 / 47497216 : ℚ) : ℝ) - Real.exp ((-1091745347 / 23748608 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_346 : sigmaPower (346 : Fin 1536) ≤ ((154055523645249 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_347 : sigmaFactor (347 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-5827613 / 126976 : ℚ) : ℝ) - Real.exp ((-23332617 / 507904 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_347 : sigmaPower (347 : Fin 1536) ≤ ((153952617932941 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_348 : sigmaFactor (348 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-362939555 / 7913472 : ℚ) : ℝ) - Real.exp ((-90821225 / 1978368 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_348 : sigmaPower (348 : Fin 1536) ≤ ((153849676711415 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_349 : sigmaFactor (349 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-2175748113 / 47472640 : ℚ) : ℝ) - Real.exp ((-4355639651 / 94945280 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_349 : sigmaPower (349 : Fin 1536) ≤ ((153746699962289 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_350 : sigmaFactor (350 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-2173859611 / 47464448 : ℚ) : ℝ) - Real.exp ((-1087965483 / 23732224 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_350 : sigmaPower (350 : Fin 1536) ≤ ((4801365239599 / 8796093022208 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_351 : sigmaFactor (351 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-45249413 / 988672 : ℚ) : ℝ) - Real.exp ((-1449361881 / 31637504 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_351 : sigmaPower (351 : Fin 1536) ≤ ((153540639807643 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_352 : sigmaFactor (352 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-135630297 / 2965504 : ℚ) : ℝ) - Real.exp ((-4242491 / 92672 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_352 : sigmaPower (352 : Fin 1536) ≤ ((76718778182647 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_353 : sigmaFactor (353 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-2168198395 / 47439872 : ℚ) : ℝ) - Real.exp ((-4340537355 / 94879744 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_353 : sigmaPower (353 : Fin 1536) ≤ ((76667218660843 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_354 : sigmaFactor (354 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-722104251 / 15810560 : ℚ) : ℝ) - Real.exp ((-361397113 / 7905280 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_354 : sigmaPower (354 : Fin 1536) ≤ ((153231282658375 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_355 : sigmaFactor (355 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-1082213913 / 23711744 : ℚ) : ℝ) - Real.exp ((-4332994787 / 94846976 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_355 : sigmaPower (355 : Fin 1536) ≤ ((38282023089225 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_356 : sigmaFactor (356 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-1081271807 / 23707648 : ℚ) : ℝ) - Real.exp ((-270576603 / 5926912 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_356 : sigmaPower (356 : Fin 1536) ≤ ((153024866398791 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_357 : sigmaFactor (357 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-720220039 / 15802368 : ℚ) : ℝ) - Real.exp ((-1441819313 / 31604736 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_357 : sigmaPower (357 : Fin 1536) ≤ ((76460802382781 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_358 : sigmaFactor (358 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-196252485 / 4308992 : ℚ) : ℝ) - Real.exp ((-98220265 / 2154496 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_358 : sigmaPower (358 : Fin 1536) ≤ ((38204576859679 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_359 : sigmaFactor (359 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-539223817 / 11847680 : ℚ) : ℝ) - Real.exp ((-4317926811 / 94781440 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_359 : sigmaPower (359 : Fin 1536) ≤ ((152714974399743 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_360 : sigmaFactor (360 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-179584493 / 3948544 : ℚ) : ℝ) - Real.exp ((-22469601 / 493568 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_360 : sigmaPower (360 : Fin 1536) ≤ ((152611605630121 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_361 : sigmaFactor (361 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-2153133279 / 47374336 : ℚ) : ℝ) - Real.exp ((-4310401403 / 94748672 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_361 : sigmaPower (361 : Fin 1536) ≤ ((152508201111313 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_362 : sigmaFactor (362 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-2151253357 / 47366144 : ℚ) : ℝ) - Real.exp ((-1076660211 / 23683072 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_362 : sigmaPower (362 : Fin 1536) ≤ ((38101190206193 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_363 : sigmaFactor (363 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-358229025 / 7892992 : ℚ) : ℝ) - Real.exp ((-1434293905 / 31571968 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_363 : sigmaPower (363 : Fin 1536) ≤ ((152301284751935 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_364 : sigmaFactor (364 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-63161637 / 1392640 : ℚ) : ℝ) - Real.exp ((-15805603 / 348160 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_364 : sigmaPower (364 : Fin 1536) ≤ ((38049443218557 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_365 : sigmaFactor (365 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-2145617881 / 47341568 : ℚ) : ℝ) - Real.exp ((-4295367747 / 94683136 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_365 : sigmaPower (365 : Fin 1536) ≤ ((152094225173065 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_366 : sigmaFactor (366 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-714580273 / 15777792 : ℚ) : ℝ) - Real.exp ((-357634409 / 7888896 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_366 : sigmaPower (366 : Fin 1536) ≤ ((75995320814923 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_367 : sigmaFactor (367 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-267733059 / 5915648 : ℚ) : ℝ) - Real.exp ((-4287859499 / 94650368 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_367 : sigmaPower (367 : Fin 1536) ≤ ((151887022225957 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_368 : sigmaFactor (368 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-267498605 / 5914624 : ℚ) : ℝ) - Real.exp ((-16734795 / 369664 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_368 : sigmaPower (368 : Fin 1536) ≤ ((151783366942773 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_369 : sigmaFactor (369 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-64791331 / 1433600 : ℚ) : ℝ) - Real.exp ((-129707787 / 2867200 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_369 : sigmaPower (369 : Fin 1536) ≤ ((18959959470207 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_370 : sigmaFactor (370 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-2136239721 / 47300608 : ℚ) : ℝ) - Real.exp ((-1069151963 / 23650304 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_370 : sigmaPower (370 : Fin 1536) ≤ ((75787974331977 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_371 : sigmaFactor (371 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-1067183117 / 23646208 : ℚ) : ℝ) - Real.exp ((-4272860163 / 94584832 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_371 : sigmaPower (371 : Fin 1536) ≤ ((75736092815501 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_372 : sigmaFactor (372 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-355415577 / 7880704 : ℚ) : ℝ) - Real.exp ((-88939873 / 1970176 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_372 : sigmaPower (372 : Fin 1536) ≤ ((151368386644123 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_373 : sigmaFactor (373 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-2130621405 / 47276032 : ℚ) : ℝ) - Real.exp ((-4265369075 / 94552064 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_373 : sigmaPower (373 : Fin 1536) ≤ ((151264551684627 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_374 : sigmaFactor (374 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-2128750063 / 47267840 : ℚ) : ℝ) - Real.exp ((-1065406419 / 23633920 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_374 : sigmaPower (374 : Fin 1536) ≤ ((151160680733811 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_375 : sigmaFactor (375 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-177239953 / 3938304 : ℚ) : ℝ) - Real.exp ((-1419294569 / 31506432 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_375 : sigmaPower (375 : Fin 1536) ≤ ((75528386886479 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_376 : sigmaFactor (376 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-531252381 / 11812864 : ℚ) : ℝ) - Real.exp ((-66470987 / 1476608 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_376 : sigmaPower (376 : Fin 1536) ≤ ((150952830783339 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_377 : sigmaFactor (377 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-2123140327 / 47243264 : ℚ) : ℝ) - Real.exp ((-4250404059 / 94486528 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_377 : sigmaPower (377 : Fin 1536) ≤ ((37712212936553 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_378 : sigmaFactor (378 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-707090615 / 15745024 : ℚ) : ℝ) - Real.exp ((-353888865 / 7872512 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_378 : sigmaPower (378 : Fin 1536) ≤ ((150744836642821 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_379 : sigmaFactor (379 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-1059702039 / 23613440 : ℚ) : ℝ) - Real.exp ((-4242930131 / 94453760 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_379 : sigmaPower (379 : Fin 1536) ≤ ((2353762272725 / 4398046511104 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_380 : sigmaFactor (380 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-96251683 / 2146304 : ℚ) : ℝ) - Real.exp ((-24086337 / 536576 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_380 : sigmaPower (380 : Fin 1536) ≤ ((150536698162165 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_381 : sigmaFactor (381 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-41483739 / 925696 : ℚ) : ℝ) - Real.exp ((-83048273 / 1851392 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_381 : sigmaPower (381 : Fin 1536) ≤ ((150432574747323 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_382 : sigmaFactor (382 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-2113805067 / 47202304 : ℚ) : ℝ) - Real.exp ((-1057932491 / 23601152 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_382 : sigmaPower (382 : Fin 1536) ≤ ((150328415191067 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_383 : sigmaFactor (383 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((7077 / 1000 : ℚ) : ℝ) * (Real.exp ((-32999065 / 737408 : ℚ) : ℝ) - Real.exp ((-4227999435 / 94388224 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_383 : sigmaPower (383 : Fin 1536) ≤ ((9389013717161 / 17592186044416 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

end LegendreK6.M2Pilot.Enclosures.Sigma002
