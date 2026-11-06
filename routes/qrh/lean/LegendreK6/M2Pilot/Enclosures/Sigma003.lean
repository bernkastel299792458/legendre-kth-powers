import LegendreK6.M2PilotDefinitions
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp

/-! Generated proposals: every bound is checked by Lean, not by trusting Arb. -/
namespace LegendreK6.M2Pilot.Enclosures.Sigma003
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem sigma_factor_upper_384 : sigmaFactor (384 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-10989979 / 245760 : ℚ) : ℝ) - Real.exp ((-85943 / 1920 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_384 : sigmaPower (384 : Fin 1536) ≤ ((150119987579017 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_385 : sigmaFactor (385 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-2108212491 / 47177728 : ℚ) : ℝ) - Real.exp ((-4220542667 / 94355456 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_385 : sigmaPower (385 : Fin 1536) ≤ ((150015719485543 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_386 : sigmaFactor (386 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-2106349729 / 47169536 : ℚ) : ℝ) - Real.exp ((-1054204107 / 23584768 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_386 : sigmaPower (386 : Fin 1536) ≤ ((149911415175295 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_387 : sigmaFactor (387 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-350747947 / 7860224 : ℚ) : ℝ) - Real.exp ((-1404363873 / 31440896 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_387 : sigmaPower (387 : Fin 1536) ≤ ((149807074629399 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_388 : sigmaFactor (388 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-1051313175 / 23576576 : ℚ) : ℝ) - Real.exp ((-263085515 / 5894144 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_388 : sigmaPower (388 : Fin 1536) ≤ ((149702697828971 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_389 : sigmaFactor (389 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-2100765733 / 47144960 : ℚ) : ℝ) - Real.exp ((-4205646291 / 94289920 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_389 : sigmaPower (389 : Fin 1536) ≤ ((149598284755111 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_390 : sigmaFactor (390 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-699635277 / 15712256 : ℚ) : ℝ) - Real.exp ((-350160481 / 7856128 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_390 : sigmaPower (390 : Fin 1536) ≤ ((74746917694453 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_391 : sigmaFactor (391 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-47660151 / 1071104 : ℚ) : ℝ) - Real.exp ((-381655153 / 8568832 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_391 : sigmaPower (391 : Fin 1536) ≤ ((149389349711433 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_392 : sigmaFactor (392 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-523797043 / 11780096 : ℚ) : ℝ) - Real.exp ((-65538891 / 1472512 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_392 : sigmaPower (392 : Fin 1536) ≤ ((149284827703751 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_393 : sigmaFactor (393 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-697776805 / 15704064 : ℚ) : ℝ) - Real.exp ((-1396924265 / 31408128 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_393 : sigmaPower (393 : Fin 1536) ≤ ((149180269346911 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_394 : sigmaFactor (394 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-2091473373 / 47104000 : ℚ) : ℝ) - Real.exp ((-1046764499 / 23552000 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_394 : sigmaPower (394 : Fin 1536) ≤ ((74537837310973 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_395 : sigmaFactor (395 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-1044808523 / 23547904 : ℚ) : ℝ) - Real.exp ((-4183344627 / 94191616 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_395 : sigmaPower (395 : Fin 1536) ≤ ((148971043509879 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_396 : sigmaFactor (396 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-347960239 / 7847936 : ℚ) : ℝ) - Real.exp ((-87075681 / 1961984 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_396 : sigmaPower (396 : Fin 1536) ≤ ((74433187995859 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_397 : sigmaFactor (397 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-2085906537 / 47079424 : ℚ) : ℝ) - Real.exp ((-4175922179 / 94158848 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_397 : sigmaPower (397 : Fin 1536) ≤ ((37190418012115 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_398 : sigmaFactor (398 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-122591315 / 2768896 : ℚ) : ℝ) - Real.exp ((-61356075 / 1384448 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_398 : sigmaPower (398 : Fin 1536) ≤ ((148656931661087 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_399 : sigmaFactor (399 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-86758287 / 1960960 : ℚ) : ℝ) - Real.exp ((-1389501817 / 31375360 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_399 : sigmaPower (399 : Fin 1536) ≤ ((18569019351321 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_400 : sigmaFactor (400 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-260043267 / 5881856 : ℚ) : ℝ) - Real.exp ((-16268747 / 367616 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_400 : sigmaPower (400 : Fin 1536) ≤ ((74223670738929 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_401 : sigmaFactor (401 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-2078494099 / 47046656 : ℚ) : ℝ) - Real.exp ((-4161094443 / 94093312 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_401 : sigmaPower (401 : Fin 1536) ≤ ((148342491643901 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_402 : sigmaFactor (402 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-62928569 / 1425408 : ℚ) : ℝ) - Real.exp ((-31495387 / 712704 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_402 : sigmaPower (402 : Fin 1536) ≤ ((148237605289625 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_403 : sigmaFactor (403 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-1037396085 / 23515136 : ℚ) : ℝ) - Real.exp ((-4153689155 / 94060544 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_403 : sigmaPower (403 : Fin 1536) ≤ ((148132682395947 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_404 : sigmaFactor (404 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-1036471139 / 23511040 : ℚ) : ℝ) - Real.exp ((-259374291 / 5877760 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_404 : sigmaPower (404 : Fin 1536) ≤ ((148027722943769 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_405 : sigmaFactor (405 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-690364367 / 15671296 : ℚ) : ℝ) - Real.exp ((-1382096529 / 31342592 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_405 : sigmaPower (405 : Fin 1536) ≤ ((73961363456991 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_406 : sigmaFactor (406 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-2069244639 / 47005696 : ℚ) : ℝ) - Real.exp ((-1035647987 / 23502848 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_406 : sigmaPower (406 : Fin 1536) ≤ ((36954423571865 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_407 : sigmaFactor (407 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-516849223 / 11749376 : ℚ) : ℝ) - Real.exp ((-4138895739 / 93995008 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_407 : sigmaPower (407 : Fin 1536) ≤ ((147712625045067 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_408 : sigmaFactor (408 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-172129155 / 3915776 : ℚ) : ℝ) - Real.exp ((-21537505 / 489472 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_408 : sigmaPower (408 : Fin 1536) ≤ ((147607519167653 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_409 : sigmaFactor (409 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-2063703543 / 46981120 : ℚ) : ℝ) - Real.exp ((-4131507611 / 93962240 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_409 : sigmaPower (409 : Fin 1536) ≤ ((36875594159013 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_410 : sigmaFactor (410 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-2061857941 / 46972928 : ℚ) : ℝ) - Real.exp ((-1031953923 / 23486464 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_410 : sigmaPower (410 : Fin 1536) ≤ ((147397197431089 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_411 : sigmaFactor (411 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-343335509 / 7827456 : ℚ) : ℝ) - Real.exp ((-1374708401 / 31309824 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_411 : sigmaPower (411 : Fin 1536) ≤ ((36822995383393 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_412 : sigmaFactor (412 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-1029084441 / 23478272 : ℚ) : ℝ) - Real.exp ((-257527259 / 5869568 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_412 : sigmaPower (412 : Fin 1536) ≤ ((73593364462149 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_413 : sigmaFactor (413 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-186938675 / 4268032 : ℚ) : ℝ) - Real.exp ((-374249865 / 8536064 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_413 : sigmaPower (413 : Fin 1536) ≤ ((9192589974003 / 17592186044416 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_414 : sigmaFactor (414 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-684827561 / 15646720 : ℚ) : ℝ) - Real.exp ((-342755193 / 7823360 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_414 : sigmaPower (414 : Fin 1536) ≤ ((146976113493593 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_415 : sigmaFactor (415 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-7546473 / 172544 : ℚ) : ℝ) - Real.exp ((-241728091 / 5521408 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_415 : sigmaPower (415 : Fin 1536) ≤ ((146870750633687 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_416 : sigmaFactor (416 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-128174959 / 2932736 : ℚ) : ℝ) - Real.exp ((-4009467 / 91648 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_416 : sigmaPower (416 : Fin 1536) ≤ ((146765350985073 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_417 : sigmaFactor (417 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-682986249 / 15638528 : ℚ) : ℝ) - Real.exp ((-1367337433 / 31277056 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_417 : sigmaPower (417 : Fin 1536) ≤ ((146659914528479 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_418 : sigmaFactor (418 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-2047118865 / 46907392 : ℚ) : ℝ) - Real.exp ((-1024582955 / 23453696 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_418 : sigmaPower (418 : Fin 1536) ≤ ((73277220622311 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_419 : sigmaFactor (419 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-1022639849 / 23449600 : ℚ) : ℝ) - Real.exp ((-4094652771 / 93798400 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_419 : sigmaPower (419 : Fin 1536) ≤ ((146448931114203 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_420 : sigmaFactor (420 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-340573541 / 7815168 : ℚ) : ℝ) - Real.exp ((-85228649 / 1953792 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_420 : sigmaPower (420 : Fin 1536) ≤ ((73171692058955 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_421 : sigmaFactor (421 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-2041603509 / 46882816 : ℚ) : ℝ) - Real.exp ((-4087298963 / 93765632 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_421 : sigmaPower (421 : Fin 1536) ≤ ((73118900118209 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_422 : sigmaFactor (422 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-2039766487 / 46874624 : ℚ) : ℝ) - Real.exp ((-1020906051 / 23437312 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_422 : sigmaPower (422 : Fin 1536) ≤ ((146132179450389 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_423 : sigmaFactor (423 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-169827515 / 3905536 : ℚ) : ℝ) - Real.exp ((-1359983625 / 31244288 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_423 : sigmaPower (423 : Fin 1536) ≤ ((73013260870235 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_424 : sigmaFactor (424 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-46274877 / 1064960 : ℚ) : ℝ) - Real.exp ((-5790169 / 133120 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_424 : sigmaPower (424 : Fin 1536) ≤ ((2280012923239 / 4398046511104 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_425 : sigmaFactor (425 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-2034259711 / 46850048 : ℚ) : ℝ) - Real.exp ((-4072608507 / 93700096 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_425 : sigmaPower (425 : Fin 1536) ≤ ((1139180433371 / 2199023255552 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_426 : sigmaFactor (426 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-677475183 / 15613952 : ℚ) : ℝ) - Real.exp ((-339078289 / 7806976 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_426 : sigmaPower (426 : Fin 1536) ≤ ((36427331718413 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_427 : sigmaFactor (427 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-1015296051 / 23416832 : ℚ) : ℝ) - Real.exp ((-4065271859 / 93667328 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_427 : sigmaPower (427 : Fin 1536) ≤ ((145603521274383 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_428 : sigmaFactor (428 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-1014379685 / 23412736 : ℚ) : ℝ) - Real.exp ((-253850355 / 5853184 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_428 : sigmaPower (428 : Fin 1536) ≤ ((145497678654261 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_429 : sigmaFactor (429 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-675642451 / 15605760 : ℚ) : ℝ) - Real.exp ((-1352646977 / 31211520 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_429 : sigmaPower (429 : Fin 1536) ≤ ((145391798993851 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_430 : sigmaFactor (430 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-2025096051 / 46809088 : ℚ) : ℝ) - Real.exp ((-1013569403 / 23404544 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_430 : sigmaPower (430 : Fin 1536) ≤ ((145285882273707 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_431 : sigmaFactor (431 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-252908183 / 5850112 : ℚ) : ℝ) - Real.exp ((-4050615723 / 93601792 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_431 : sigmaPower (431 : Fin 1536) ≤ ((145179928474369 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_432 : sigmaFactor (432 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-4954499 / 114688 : ℚ) : ℝ) - Real.exp ((-309969 / 7168 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_432 : sigmaPower (432 : Fin 1536) ≤ ((145073937576361 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_433 : sigmaFactor (433 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-2019606435 / 46784512 : ℚ) : ℝ) - Real.exp ((-4043296235 / 93569024 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_433 : sigmaPower (433 : Fin 1536) ≤ ((36241977390049 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_434 : sigmaFactor (434 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-2017777993 / 46776320 : ℚ) : ℝ) - Real.exp ((-1009909659 / 23388160 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_434 : sigmaPower (434 : Fin 1536) ≤ ((36215461101593 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_435 : sigmaFactor (435 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-30544701 / 708608 : ℚ) : ℝ) - Real.exp ((-122302499 / 2834432 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_435 : sigmaPower (435 : Fin 1536) ≤ ((72377871047687 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_436 : sigmaFactor (436 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-1007061627 / 23379968 : ℚ) : ℝ) - Real.exp ((-252020483 / 5844992 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_436 : sigmaPower (436 : Fin 1536) ≤ ((18081200325959 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_437 : sigmaFactor (437 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-2012296957 / 46751744 : ℚ) : ℝ) - Real.exp ((-4028674419 / 93503488 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_437 : sigmaPower (437 : Fin 1536) ≤ ((144543425923725 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_438 : sigmaFactor (438 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-670157125 / 15581184 : ℚ) : ℝ) - Real.exp ((-335418545 / 7790592 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_438 : sigmaPower (438 : Fin 1536) ≤ ((144437212023975 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_439 : sigmaFactor (439 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-502161627 / 11683840 : ℚ) : ℝ) - Real.exp ((-4021372091 / 93470720 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_439 : sigmaPower (439 : Fin 1536) ≤ ((144330960888853 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_440 : sigmaFactor (440 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-501705589 / 11681792 : ℚ) : ℝ) - Real.exp ((-62776923 / 1460224 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_440 : sigmaPower (440 : Fin 1536) ≤ ((144224672498775 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_441 : sigmaFactor (441 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-668332973 / 15572992 : ℚ) : ℝ) - Real.exp ((-1338025161 / 31145984 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_441 : sigmaPower (441 : Fin 1536) ≤ ((144118346834143 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_442 : sigmaFactor (442 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-2003176197 / 46710784 : ℚ) : ℝ) - Real.exp ((-1002607331 / 23355392 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_442 : sigmaPower (442 : Fin 1536) ≤ ((72005991937673 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_443 : sigmaFactor (443 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-1000677095 / 23351296 : ℚ) : ℝ) - Real.exp ((-4006784595 / 93405184 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_443 : sigmaPower (443 : Fin 1536) ≤ ((143905583602759 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_444 : sigmaFactor (444 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-333255483 / 7782400 : ℚ) : ℝ) - Real.exp ((-83398777 / 1945600 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_444 : sigmaPower (444 : Fin 1536) ≤ ((143799145996743 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_445 : sigmaFactor (445 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-1997712321 / 46686208 : ℚ) : ℝ) - Real.exp ((-3999499427 / 93372416 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_445 : sigmaPower (445 : Fin 1536) ≤ ((143692671037645 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_446 : sigmaFactor (446 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-181444769 / 4243456 : ℚ) : ℝ) - Real.exp ((-90814977 / 2121728 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_446 : sigmaPower (446 : Fin 1536) ≤ ((143586158705799 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_447 : sigmaFactor (447 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-20771597 / 486144 : ℚ) : ℝ) - Real.exp ((-1330739993 / 31113216 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_447 : sigmaPower (447 : Fin 1536) ≤ ((143479608981525 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_448 : sigmaFactor (448 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-62257965 / 1458176 : ℚ) : ℝ) - Real.exp ((-973775 / 22784 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_448 : sigmaPower (448 : Fin 1536) ≤ ((143373021845129 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_449 : sigmaFactor (449 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-117084539 / 2744320 : ℚ) : ℝ) - Real.exp ((-234408603 / 5488640 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_449 : sigmaPower (449 : Fin 1536) ≤ ((71633198638451 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_450 : sigmaFactor (450 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-662873387 / 15548416 : ℚ) : ℝ) - Real.exp ((-331775961 / 7774208 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_450 : sigmaPower (450 : Fin 1536) ≤ ((35789933814281 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_451 : sigmaFactor (451 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-993401937 / 23318528 : ℚ) : ℝ) - Real.exp ((-3977678243 / 93274112 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_451 : sigmaPower (451 : Fin 1536) ≤ ((71526517883029 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_452 : sigmaFactor (452 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-992494151 / 23314432 : ℚ) : ℝ) - Real.exp ((-248377899 / 5828608 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_452 : sigmaPower (452 : Fin 1536) ≤ ((142946298783955 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_453 : sigmaFactor (453 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-661057815 / 15540224 : ℚ) : ℝ) - Real.exp ((-1323471985 / 31080448 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_453 : sigmaPower (453 : Fin 1536) ≤ ((35709881072763 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_454 : sigmaFactor (454 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-1981359303 / 46612480 : ℚ) : ℝ) - Real.exp ((-991696739 / 23306240 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_454 : sigmaPower (454 : Fin 1536) ≤ ((35683178066893 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_455 : sigmaFactor (455 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-494886469 / 11651072 : ℚ) : ℝ) - Real.exp ((-3963159387 / 93208576 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_455 : sigmaPower (455 : Fin 1536) ≤ ((71312931346861 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_456 : sigmaFactor (456 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-164811097 / 3883008 : ℚ) : ℝ) - Real.exp ((-20622569 / 485376 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_456 : sigmaPower (456 : Fin 1536) ≤ ((35629743887425 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_457 : sigmaFactor (457 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-16329927 / 385024 : ℚ) : ℝ) - Real.exp ((-32693459 / 770048 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_457 : sigmaPower (457 : Fin 1536) ≤ ((35603012703921 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_458 : sigmaFactor (458 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-1974109885 / 46579712 : ℚ) : ℝ) - Real.exp ((-988071315 / 23289856 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_458 : sigmaPower (458 : Fin 1536) ≤ ((142305088471843 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_459 : sigmaFactor (459 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-328716553 / 7761920 : ℚ) : ℝ) - Real.exp ((-1316221137 / 31047680 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_459 : sigmaPower (459 : Fin 1536) ≤ ((71099044249165 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_460 : sigmaFactor (460 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-985244733 / 23281664 : ℚ) : ℝ) - Real.exp ((-246565187 / 5820416 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_460 : sigmaPower (460 : Fin 1536) ≤ ((35522762718821 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_461 : sigmaFactor (461 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-1968680329 / 46555136 : ℚ) : ℝ) - Real.exp ((-3941424003 / 93110272 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_461 : sigmaPower (461 : Fin 1536) ≤ ((141983975582829 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_462 : sigmaFactor (462 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-655623969 / 15515648 : ℚ) : ℝ) - Real.exp ((-328150537 / 7757824 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_462 : sigmaPower (462 : Fin 1536) ≤ ((141876862601077 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_463 : sigmaFactor (463 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-245633025 / 5817344 : ℚ) : ℝ) - Real.exp ((-3934190315 / 93077504 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_463 : sigmaPower (463 : Fin 1536) ≤ ((70884855955063 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_464 : sigmaFactor (464 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-245407151 / 5816320 : ℚ) : ℝ) - Real.exp ((-15353811 / 363520 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_464 : sigmaPower (464 : Fin 1536) ≤ ((70831261745029 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_465 : sigmaFactor (465 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-653816977 / 15507456 : ℚ) : ℝ) - Real.exp ((-1308987449 / 31014912 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_465 : sigmaPower (465 : Fin 1536) ≤ ((141555297320943 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_466 : sigmaFactor (466 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-115273257 / 2736128 : ℚ) : ℝ) - Real.exp ((-57696331 / 1368064 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_466 : sigmaPower (466 : Fin 1536) ≤ ((35362008345709 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_467 : sigmaFactor (467 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-978920261 / 23252992 : ℚ) : ℝ) - Real.exp ((-3919740099 / 93011968 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_467 : sigmaPower (467 : Fin 1536) ≤ ((141340731655777 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_468 : sigmaFactor (468 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-29636915 / 704512 : ℚ) : ℝ) - Real.exp ((-7416915 / 176128 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_468 : sigmaPower (468 : Fin 1536) ≤ ((70616696059897 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_469 : sigmaFactor (469 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-1954232973 / 46489600 : ℚ) : ℝ) - Real.exp ((-3912523571 / 92979200 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_469 : sigmaPower (469 : Fin 1536) ≤ ((35281503688725 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_470 : sigmaFactor (470 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-1952430271 / 46481408 : ℚ) : ℝ) - Real.exp ((-977229363 / 23240704 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_470 : sigmaPower (470 : Fin 1536) ≤ ((141018599541093 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_471 : sigmaFactor (471 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-162552357 / 3872768 : ℚ) : ℝ) - Real.exp ((-1301770921 / 30982144 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_471 : sigmaPower (471 : Fin 1536) ≤ ((70455573229179 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_472 : sigmaFactor (472 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-487206753 / 11616256 : ℚ) : ℝ) - Real.exp ((-60964211 / 1452032 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_472 : sigmaPower (472 : Fin 1536) ≤ ((70401827743333 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_473 : sigmaFactor (473 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-1947026455 / 46456832 : ℚ) : ℝ) - Real.exp ((-3898107675 / 92913664 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_473 : sigmaPower (473 : Fin 1536) ≤ ((140696126605973 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_474 : sigmaFactor (474 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-648408871 / 15482880 : ℚ) : ℝ) - Real.exp ((-324542273 / 7741440 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_474 : sigmaPower (474 : Fin 1536) ≤ ((70294279898111 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_475 : sigmaFactor (475 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-971713743 / 23220224 : ℚ) : ℝ) - Real.exp ((-3890908307 / 92880896 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_475 : sigmaPower (475 : Fin 1536) ≤ ((140480955037341 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_476 : sigmaFactor (476 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-970814537 / 23216128 : ℚ) : ℝ) - Real.exp ((-242956923 / 5804032 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_476 : sigmaPower (476 : Fin 1536) ≤ ((140373312309243 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_477 : sigmaFactor (477 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-646610459 / 15474688 : ℚ) : ℝ) - Real.exp ((-1294571553 / 30949376 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_477 : sigmaPower (477 : Fin 1536) ≤ ((140265631591829 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_478 : sigmaFactor (478 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-1938034395 / 46415872 : ℚ) : ℝ) - Real.exp ((-970029995 / 23207936 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_478 : sigmaPower (478 : Fin 1536) ≤ ((17519739108123 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_479 : sigmaFactor (479 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-11001353 / 263680 : ℚ) : ℝ) - Real.exp ((-352411521 / 8437760 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_479 : sigmaPower (479 : Fin 1536) ≤ ((35012539027145 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_480 : sigmaFactor (480 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-40300887 / 966656 : ℚ) : ℝ) - Real.exp ((-1260721 / 30208 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_480 : sigmaPower (480 : Fin 1536) ≤ ((69971180651237 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_481 : sigmaFactor (481 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-1932647739 / 46391296 : ℚ) : ℝ) - Real.exp ((-3869344523 / 92782592 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_481 : sigmaPower (481 : Fin 1536) ≤ ((34958632106627 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_482 : sigmaFactor (482 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-1930853617 / 46383104 : ℚ) : ℝ) - Real.exp ((-966438891 / 23191552 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_482 : sigmaPower (482 : Fin 1536) ≤ ((4366458045641 / 8796093022208 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_483 : sigmaFactor (483 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-18912355 / 454656 : ℚ) : ℝ) - Real.exp ((-75728785 / 1818624 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_483 : sigmaPower (483 : Fin 1536) ≤ ((34904687096075 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_484 : sigmaFactor (484 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-963633759 / 23183360 : ℚ) : ℝ) - Real.exp ((-241161371 / 5795840 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_484 : sigmaPower (484 : Fin 1536) ≤ ((139510801177673 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_485 : sigmaFactor (485 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-1925475541 / 46358528 : ℚ) : ℝ) - Real.exp ((-3854997267 / 92717056 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_485 : sigmaPower (485 : Fin 1536) ≤ ((1089084498597 / 2199023255552 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_486 : sigmaFactor (486 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-641228093 / 15450112 : ℚ) : ℝ) - Real.exp ((-320951169 / 7725056 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_486 : sigmaPower (486 : Fin 1536) ≤ ((139294792292301 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_487 : sigmaFactor (487 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-480473433 / 11585536 : ℚ) : ℝ) - Real.exp ((-3847832219 / 92684288 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_487 : sigmaPower (487 : Fin 1536) ≤ ((139186730573085 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_488 : sigmaFactor (488 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-480025975 / 11583488 : ℚ) : ℝ) - Real.exp ((-60066435 / 1447936 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_488 : sigmaPower (488 : Fin 1536) ≤ ((8692414415157 / 17592186044416 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_489 : sigmaFactor (489 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-639438261 / 15441920 : ℚ) : ℝ) - Real.exp ((-1280224297 / 30883840 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_489 : sigmaPower (489 : Fin 1536) ≤ ((69485246240155 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_490 : sigmaFactor (490 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-174229671 / 4210688 : ℚ) : ℝ) - Real.exp ((-87206713 / 2105344 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_490 : sigmaPower (490 : Fin 1536) ≤ ((69431158033097 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_491 : sigmaFactor (491 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-957369347 / 23154688 : ℚ) : ℝ) - Real.exp ((-3833519283 / 92618752 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_491 : sigmaPower (491 : Fin 1536) ≤ ((138754101379863 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_492 : sigmaFactor (492 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-318825287 / 7716864 : ℚ) : ℝ) - Real.exp ((-79790513 / 1929216 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_492 : sigmaPower (492 : Fin 1536) ≤ ((138645848401003 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_493 : sigmaFactor (493 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-1911165465 / 46292992 : ℚ) : ℝ) - Real.exp ((-3826371395 / 92585984 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_493 : sigmaPower (493 : Fin 1536) ≤ ((69268778554643 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_494 : sigmaFactor (494 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-1909379923 / 46284800 : ℚ) : ℝ) - Real.exp ((-955699899 / 23142400 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_494 : sigmaPower (494 : Fin 1536) ≤ ((8651826717773 / 17592186044416 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_495 : sigmaFactor (495 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-79483129 / 1928192 : ℚ) : ℝ) - Real.exp ((-1273076409 / 30851072 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_495 : sigmaPower (495 : Fin 1536) ≤ ((34580214876473 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_496 : sigmaFactor (496 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-238226373 / 5783552 : ℚ) : ℝ) - Real.exp ((-14904923 / 361472 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_496 : sigmaPower (496 : Fin 1536) ≤ ((69106226576743 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_497 : sigmaFactor (497 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-1904027587 / 46260224 : ℚ) : ℝ) - Real.exp ((-3812092779 / 92520448 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_497 : sigmaPower (497 : Fin 1536) ≤ ((34526002101691 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_498 : sigmaFactor (498 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-634081635 / 15417344 : ℚ) : ℝ) - Real.exp ((-317377225 / 7708672 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_498 : sigmaPower (498 : Fin 1536) ≤ ((34498881311331 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_499 : sigmaFactor (499 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-950231469 / 23121920 : ℚ) : ℝ) - Real.exp ((-3804962051 / 92487680 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_499 : sigmaPower (499 : Fin 1536) ≤ ((8617937728047 / 17592186044416 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_500 : sigmaFactor (500 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-55843579 / 1359872 : ℚ) : ℝ) - Real.exp ((-13975731 / 339968 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_500 : sigmaPower (500 : Fin 1536) ≤ ((137778443596617 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_501 : sigmaFactor (501 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-57481853 / 1400832 : ℚ) : ℝ) - Real.exp ((-115085971 / 2801664 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_501 : sigmaPower (501 : Fin 1536) ≤ ((137669845068477 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_502 : sigmaFactor (502 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-1895121327 / 46219264 : ℚ) : ℝ) - Real.exp ((-948569171 / 23109632 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_502 : sigmaPower (502 : Fin 1536) ≤ ((137561208043871 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_503 : sigmaFactor (503 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-473335555 / 11552768 : ℚ) : ℝ) - Real.exp ((-3790717755 / 92422144 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_503 : sigmaPower (503 : Fin 1536) ≤ ((68726266251163 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_504 : sigmaFactor (504 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-157630319 / 3850240 : ℚ) : ℝ) - Real.exp ((-19724793 / 481280 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_504 : sigmaPower (504 : Fin 1536) ≤ ((34335954605839 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_505 : sigmaFactor (505 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-1889786151 / 46194688 : ℚ) : ℝ) - Real.exp ((-3783604187 / 92389376 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_505 : sigmaPower (505 : Fin 1536) ≤ ((137235065786457 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_506 : sigmaFactor (506 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-1888009189 / 46186496 : ℚ) : ℝ) - Real.exp ((-945012387 / 23093248 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_506 : sigmaPower (506 : Fin 1536) ≤ ((68563137285557 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_507 : sigmaFactor (507 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-314372157 / 7696384 : ℚ) : ℝ) - Real.exp ((-1258832113 / 30785536 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_507 : sigmaPower (507 : Fin 1536) ≤ ((137017444756793 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_508 : sigmaFactor (508 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-942228705 / 23085056 : ℚ) : ℝ) - Real.exp ((-235809035 / 5771264 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_508 : sigmaPower (508 : Fin 1536) ≤ ((68454288161475 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_509 : sigmaFactor (509 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-1882682593 / 46161920 : ℚ) : ℝ) - Real.exp ((-3769394211 / 92323840 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_509 : sigmaPower (509 : Fin 1536) ≤ ((133593427001 / 274877906944 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_510 : sigmaFactor (510 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-626969497 / 15384576 : ℚ) : ℝ) - Real.exp ((-313820441 / 7692288 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_510 : sigmaPower (510 : Fin 1536) ≤ ((17086340439305 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_511 : sigmaFactor (511 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1637 / 200 : ℚ) : ℝ) * (Real.exp ((-14680743 / 360512 : ℚ) : ℝ) - Real.exp ((-3762297803 / 92291072 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_511 : sigmaPower (511 : Fin 1536) ≤ ((136581739098609 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

end LegendreK6.M2Pilot.Enclosures.Sigma003
