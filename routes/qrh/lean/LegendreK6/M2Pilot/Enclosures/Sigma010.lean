import LegendreK6.M2PilotDefinitions
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp

/-! Generated proposals: every bound is checked by Lean, not by trusting Arb. -/
namespace LegendreK6.M2Pilot.Enclosures.Sigma010
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem sigma_factor_upper_1280 : sigmaFactor (1280 : Fin 1536) ≤ ((2759861 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-5680367 / 311296 : ℚ) : ℝ) - Real.exp ((-11121 / 608 : ℚ) : ℝ)) ≤ ((2759861 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1280 : sigmaPower (1280 : Fin 1536) ≤ ((39505259889215 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1281 : sigmaFactor (1281 : Fin 1536) ≤ ((2835231 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-241954713 / 13279232 : ℚ) : ℝ) - Real.exp ((-485068441 / 26558464 : ℚ) : ℝ)) ≤ ((2835231 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1281 : sigmaPower (1281 : Fin 1536) ≤ ((39359034374511 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1282 : sigmaFactor (1282 : Fin 1536) ≤ ((22755 / 2199023255552 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-3875091 / 212992 : ℚ) : ℝ) - Real.exp ((-1942193 / 106496 : ℚ) : ℝ)) ≤ ((22755 / 2199023255552 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1282 : sigmaPower (1282 : Fin 1536) ≤ ((9803187177363 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1283 : sigmaFactor (1283 : Fin 1536) ≤ ((2992141 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-361710305 / 19910656 : ℚ) : ℝ) - Real.exp ((-1450316835 / 79642624 : ℚ) : ℝ)) ≤ ((2992141 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1283 : sigmaPower (1283 : Fin 1536) ≤ ((19533201428457 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1284 : sigmaFactor (1284 : Fin 1536) ≤ ((12007 / 1099511627776 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-120366653 / 6635520 : ℚ) : ℝ) - Real.exp ((-30164057 / 1658880 : ℚ) : ℝ)) ≤ ((12007 / 1099511627776 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1284 : sigmaPower (1284 : Fin 1536) ≤ ((19459998389873 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1285 : sigmaFactor (1285 : Fin 1536) ≤ ((197353 / 17592186044416 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-720979941 / 39804928 : ℚ) : ℝ) - Real.exp ((-1445434067 / 79609856 : ℚ) : ℝ)) ≤ ((197353 / 17592186044416 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1285 : sigmaPower (1285 : Fin 1536) ≤ ((38773530440763 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1286 : sigmaFactor (1286 : Fin 1536) ≤ ((1621885 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-719760679 / 39796736 : ℚ) : ℝ) - Real.exp ((-360748707 / 19898368 : ℚ) : ℝ)) ≤ ((1621885 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1286 : sigmaPower (1286 : Fin 1536) ≤ ((38627003802753 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1287 : sigmaFactor (1287 : Fin 1536) ≤ ((1666109 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-59878511 / 3315712 : ℚ) : ℝ) - Real.exp ((-480185673 / 26525696 : ℚ) : ℝ)) ≤ ((1666109 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1287 : sigmaPower (1287 : Fin 1536) ≤ ((19240208414235 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1288 : sigmaFactor (1288 : Fin 1536) ≤ ((1711527 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-179331075 / 9945088 : ℚ) : ℝ) - Real.exp ((-22470635 / 1243136 : ℚ) : ℝ)) ≤ ((1711527 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1288 : sigmaPower (1288 : Fin 1536) ≤ ((38333769480639 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1289 : sigmaFactor (1289 : Fin 1536) ≤ ((1758171 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-716107183 / 39772160 : ℚ) : ℝ) - Real.exp ((-1435685691 / 79544320 : ℚ) : ℝ)) ≤ ((1758171 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1289 : sigmaPower (1289 : Fin 1536) ≤ ((19093530860977 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1290 : sigmaFactor (1290 : Fin 1536) ≤ ((3612147 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-238296927 / 13254656 : ℚ) : ℝ) - Real.exp ((-119437681 / 6627328 : ℚ) : ℝ)) ≤ ((3612147 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1290 : sigmaPower (1290 : Fin 1536) ≤ ((38040293515079 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1291 : sigmaFactor (1291 : Fin 1536) ≤ ((3710537 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-356837547 / 19877888 : ℚ) : ℝ) - Real.exp ((-1430820083 / 79511552 : ℚ) : ℝ)) ≤ ((3710537 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1291 : sigmaPower (1291 : Fin 1536) ≤ ((37893464822645 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1292 : sigmaFactor (1292 : Fin 1536) ≤ ((3811581 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-356230061 / 19873792 : ℚ) : ℝ) - Real.exp ((-89274339 / 4968448 : ℚ) : ℝ)) ≤ ((3811581 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1292 : sigmaPower (1292 : Fin 1536) ≤ ((37746575607255 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1293 : sigmaFactor (1293 : Fin 1536) ≤ ((3915349 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-21552905 / 1204224 : ℚ) : ℝ) - Real.exp ((-43210915 / 2408448 : ℚ) : ℝ)) ≤ ((3915349 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1293 : sigmaPower (1293 : Fin 1536) ≤ ((4699953228935 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1294 : sigmaFactor (1294 : Fin 1536) ≤ ((4021915 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-710032323 / 39731200 : ℚ) : ℝ) - Real.exp ((-355883099 / 19865600 : ℚ) : ℝ)) ≤ ((4021915 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1294 : sigmaPower (1294 : Fin 1536) ≤ ((18726307728929 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1295 : sigmaFactor (1295 : Fin 1536) ≤ ((516419 / 35184372088832 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-88602437 / 4965376 : ℚ) : ℝ) - Real.exp ((-1421106027 / 79446016 : ℚ) : ℝ)) ≤ ((516419 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1295 : sigmaPower (1295 : Fin 1536) ≤ ((9326386112225 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1296 : sigmaFactor (1296 : Fin 1536) ≤ ((2121869 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-29483641 / 1654784 : ℚ) : ℝ) - Real.exp ((-1847241 / 103424 : ℚ) : ℝ)) ≤ ((2121869 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1296 : sigmaPower (1296 : Fin 1536) ≤ ((9289603191771 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1297 : sigmaFactor (1297 : Fin 1536) ≤ ((2179575 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-706395987 / 39706624 : ℚ) : ℝ) - Real.exp ((-1416257579 / 79413248 : ℚ) : ℝ)) ≤ ((2179575 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1297 : sigmaPower (1297 : Fin 1536) ≤ ((4626402546857 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1298 : sigmaFactor (1298 : Fin 1536) ≤ ((4477671 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-705185305 / 39698432 : ℚ) : ℝ) - Real.exp ((-353458875 / 19849216 : ℚ) : ℝ)) ≤ ((4477671 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1298 : sigmaPower (1298 : Fin 1536) ≤ ((36863967234633 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1299 : sigmaFactor (1299 : Fin 1536) ≤ ((2299691 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-6901719 / 389120 : ℚ) : ℝ) - Real.exp ((-27674801 / 1556480 : ℚ) : ℝ)) ≤ ((2299691 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1299 : sigmaPower (1299 : Fin 1536) ≤ ((286848853975 / 2199023255552 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1300 : sigmaFactor (1300 : Fin 1536) ≤ ((295273 / 17592186044416 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-351383043 / 19841024 : ℚ) : ℝ) - Real.exp ((-88062227 / 4960256 : ℚ) : ℝ)) ≤ ((295273 / 17592186044416 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1300 : sigmaPower (1300 : Fin 1536) ≤ ((36569278559711 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1301 : sigmaFactor (1301 : Fin 1536) ≤ ((4852717 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-701557549 / 39673856 : ℚ) : ℝ) - Real.exp ((-1406577843 / 79347712 : ℚ) : ℝ)) ≤ ((4852717 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1301 : sigmaPower (1301 : Fin 1536) ≤ ((18210921474845 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1302 : sigmaFactor (1302 : Fin 1536) ≤ ((4984519 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-233449909 / 13221888 : ℚ) : ℝ) - Real.exp ((-117013457 / 6610944 : ℚ) : ℝ)) ≤ ((4984519 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1302 : sigmaPower (1302 : Fin 1536) ≤ ((36274346441027 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1303 : sigmaFactor (1303 : Fin 1536) ≤ ((639983 / 35184372088832 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-174785655 / 9914368 : ℚ) : ℝ) - Real.exp ((-1401746555 / 79314944 : ℚ) : ℝ)) ≤ ((639983 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1303 : sigmaPower (1303 : Fin 1536) ≤ ((2257924312249 / 17592186044416 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1304 : sigmaFactor (1304 : Fin 1536) ≤ ((164339 / 8796093022208 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-1442017 / 81920 : ℚ) : ℝ) - Real.exp ((-180699 / 10240 : ℚ) : ℝ)) ≤ ((164339 / 8796093022208 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1304 : sigmaPower (1304 : Fin 1536) ≤ ((17989585288395 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1305 : sigmaFactor (1305 : Fin 1536) ≤ ((5401567 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-232243517 / 13213696 : ℚ) : ℝ) - Real.exp ((-465640329 / 26427392 : ℚ) : ℝ)) ≤ ((5401567 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1305 : sigmaPower (1305 : Fin 1536) ≤ ((35831491145643 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1306 : sigmaFactor (1306 : Fin 1536) ≤ ((5548121 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-695525589 / 39632896 : ℚ) : ℝ) - Real.exp ((-348627587 / 19816448 : ℚ) : ℝ)) ≤ ((5548121 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1306 : sigmaPower (1306 : Fin 1536) ≤ ((35683750664711 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1307 : sigmaFactor (1307 : Fin 1536) ≤ ((5698611 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-347160671 / 19812352 : ℚ) : ℝ) - Real.exp ((-1392101139 / 79249408 : ℚ) : ℝ)) ≤ ((5698611 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1307 : sigmaPower (1307 : Fin 1536) ≤ ((35535949096129 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1308 : sigmaFactor (1308 : Fin 1536) ≤ ((5853143 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-115519635 / 6602752 : ℚ) : ℝ) - Real.exp ((-28951945 / 1650688 : ℚ) : ℝ)) ≤ ((5853143 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1308 : sigmaPower (1308 : Fin 1536) ≤ ((17694043201001 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1309 : sigmaFactor (1309 : Fin 1536) ≤ ((6011823 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-691914993 / 39608320 : ℚ) : ℝ) - Real.exp ((-1387287011 / 79216640 : ℚ) : ℝ)) ≤ ((6011823 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1309 : sigmaPower (1309 : Fin 1536) ≤ ((35240162544403 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1310 : sigmaFactor (1310 : Fin 1536) ≤ ((6174761 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-690712891 / 39600128 : ℚ) : ℝ) - Real.exp ((-346220523 / 19800064 : ℚ) : ℝ)) ≤ ((6174761 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1310 : sigmaPower (1310 : Fin 1536) ≤ ((35092177485373 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1311 : sigmaFactor (1311 : Fin 1536) ≤ ((792759 / 35184372088832 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-14364823 / 824832 : ℚ) : ℝ) - Real.exp ((-460826201 / 26394624 : ℚ) : ℝ)) ≤ ((792759 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1311 : sigmaPower (1311 : Fin 1536) ≤ ((17472065593461 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1312 : sigmaFactor (1312 : Fin 1536) ≤ ((3256935 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-43019427 / 2473984 : ℚ) : ℝ) - Real.exp ((-1347731 / 77312 : ℚ) : ℝ)) ≤ ((3256935 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1312 : sigmaPower (1312 : Fin 1536) ≤ ((34796023611031 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1313 : sigmaFactor (1313 : Fin 1536) ≤ ((6690275 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-687110875 / 39575552 : ℚ) : ℝ) - Real.exp ((-1377675915 / 79151104 : ℚ) : ℝ)) ≤ ((6690275 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1313 : sigmaPower (1313 : Fin 1536) ≤ ((34647854719645 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1314 : sigmaFactor (1314 : Fin 1536) ≤ ((3435705 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-228637211 / 13189120 : ℚ) : ℝ) - Real.exp ((-114606393 / 6594560 : ℚ) : ℝ)) ≤ ((3435705 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1314 : sigmaPower (1314 : Fin 1536) ≤ ((34499624474681 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1315 : sigmaFactor (1315 : Fin 1536) ≤ ((7057399 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-31123323 / 1798144 : ℚ) : ℝ) - Real.exp ((-124807177 / 7192576 : ℚ) : ℝ)) ≤ ((7057399 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1315 : sigmaPower (1315 : Fin 1536) ≤ ((4293916604753 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1316 : sigmaFactor (1316 : Fin 1536) ≤ ((7248371 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-20103391 / 1163264 : ℚ) : ℝ) - Real.exp ((-5038539 / 290816 : ℚ) : ℝ)) ≤ ((7248371 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1316 : sigmaPower (1316 : Fin 1536) ≤ ((34202979771525 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1317 : sigmaFactor (1317 : Fin 1536) ≤ ((7444459 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-227439399 / 13180928 : ℚ) : ℝ) - Real.exp ((-456029233 / 26361856 : ℚ) : ℝ)) ≤ ((7444459 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1317 : sigmaPower (1317 : Fin 1536) ≤ ((34054565237005 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1318 : sigmaFactor (1318 : Fin 1536) ≤ ((7645797 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-681121815 / 39534592 : ℚ) : ℝ) - Real.exp ((-341423555 / 19767296 : ℚ) : ℝ)) ≤ ((7645797 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1318 : sigmaPower (1318 : Fin 1536) ≤ ((1059565287383 / 8796093022208 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1319 : sigmaFactor (1319 : Fin 1536) ≤ ((3926263 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-169981537 / 9881600 : ℚ) : ℝ) - Real.exp ((-1363302171 / 79052800 : ℚ) : ℝ)) ≤ ((3926263 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1319 : sigmaPower (1319 : Fin 1536) ≤ ((33757551611033 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1320 : sigmaFactor (1320 : Fin 1536) ≤ ((2016197 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-56560933 / 3293184 : ℚ) : ℝ) - Real.exp ((-7088081 / 411648 : ℚ) : ℝ)) ≤ ((2016197 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1320 : sigmaPower (1320 : Fin 1536) ≤ ((4201119055383 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1321 : sigmaFactor (1321 : Fin 1536) ≤ ((8282729 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-677536959 / 39510016 : ℚ) : ℝ) - Real.exp ((-1358522363 / 79020032 : ℚ) : ℝ)) ≤ ((8282729 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1321 : sigmaPower (1321 : Fin 1536) ≤ ((16730145827021 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1322 : sigmaFactor (1322 : Fin 1536) ≤ ((2126625 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-676343437 / 39501824 : ℚ) : ℝ) - Real.exp ((-339033651 / 19750912 : ℚ) : ℝ)) ≤ ((2126625 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1322 : sigmaPower (1322 : Fin 1536) ≤ ((16655784602815 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1323 : sigmaFactor (1323 : Fin 1536) ≤ ((4368127 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-112525105 / 6582272 : ℚ) : ℝ) - Real.exp ((-451249425 / 26329088 : ℚ) : ℝ)) ≤ ((4368127 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1323 : sigmaPower (1323 : Fin 1536) ≤ ((8290696264865 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1324 : sigmaFactor (1324 : Fin 1536) ≤ ((8972151 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-336979269 / 19742720 : ℚ) : ℝ) - Real.exp ((-84460211 / 4935680 : ℚ) : ℝ)) ≤ ((8972151 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1324 : sigmaPower (1324 : Fin 1536) ≤ ((33013939177129 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1325 : sigmaFactor (1325 : Fin 1536) ≤ ((9214353 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-672767161 / 39477248 : ℚ) : ℝ) - Real.exp ((-1348979907 / 78954496 : ℚ) : ℝ)) ≤ ((9214353 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1325 : sigmaPower (1325 : Fin 1536) ≤ ((8216257880051 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1326 : sigmaFactor (1326 : Fin 1536) ≤ ((4731513 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-20350803 / 1196032 : ℚ) : ℝ) - Real.exp ((-10201499 / 598016 : ℚ) : ℝ)) ≤ ((4731513 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1326 : sigmaPower (1326 : Fin 1536) ≤ ((16358031025111 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1327 : sigmaFactor (1327 : Fin 1536) ≤ ((4859171 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-83798319 / 4932608 : ℚ) : ℝ) - Real.exp ((-1344217259 / 78921728 : ℚ) : ℝ)) ≤ ((4859171 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1327 : sigmaPower (1327 : Fin 1536) ≤ ((32567030728685 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1328 : sigmaFactor (1328 : Fin 1536) ≤ ((9980475 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-83649665 / 4931584 : ℚ) : ℝ) - Real.exp ((-5241555 / 308224 : ℚ) : ℝ)) ≤ ((9980475 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1328 : sigmaPower (1328 : Fin 1536) ≤ ((4052242189633 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1329 : sigmaFactor (1329 : Fin 1536) ≤ ((10249607 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-222669601 / 13148160 : ℚ) : ℝ) - Real.exp ((-446486777 / 26296320 : ℚ) : ℝ)) ≤ ((10249607 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1329 : sigmaPower (1329 : Fin 1536) ≤ ((16134391188399 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1330 : sigmaFactor (1330 : Fin 1536) ≤ ((5262961 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-666821001 / 39436288 : ℚ) : ℝ) - Real.exp ((-334271003 / 19718144 : ℚ) : ℝ)) ≤ ((5262961 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1330 : sigmaPower (1330 : Fin 1536) ≤ ((2007472829331 / 17592186044416 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1331 : sigmaFactor (1331 : Fin 1536) ≤ ((10809609 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-332816957 / 19714048 : ℚ) : ℝ) - Real.exp ((-1334709123 / 78856192 : ℚ) : ℝ)) ≤ ((10809609 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1331 : sigmaPower (1331 : Fin 1536) ≤ ((31970286155931 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1332 : sigmaFactor (1332 : Fin 1536) ≤ ((11100863 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-110741257 / 6569984 : ℚ) : ℝ) - Real.exp ((-27756993 / 1642496 : ℚ) : ℝ)) ≤ ((11100863 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1332 : sigmaPower (1332 : Fin 1536) ≤ ((15910472499023 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1333 : sigmaFactor (1333 : Fin 1536) ≤ ((2849971 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-39015405 / 2318336 : ℚ) : ℝ) - Real.exp ((-78233155 / 4636672 : ℚ) : ℝ)) ≤ ((2849971 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1333 : sigmaPower (1333 : Fin 1536) ≤ ((15835770878477 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1334 : sigmaFactor (1334 : Fin 1536) ≤ ((2926719 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-662076943 / 39403520 : ℚ) : ℝ) - Real.exp ((-331898259 / 19701760 : ℚ) : ℝ)) ≤ ((2926719 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1334 : sigmaPower (1334 : Fin 1536) ≤ ((31522076393931 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1335 : sigmaFactor (1335 : Fin 1536) ≤ ((6011025 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-55074393 / 3282944 : ℚ) : ℝ) - Real.exp ((-441741289 / 26263552 : ℚ) : ℝ)) ≤ ((6011025 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1335 : sigmaPower (1335 : Fin 1536) ≤ ((31372548870225 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1336 : sigmaFactor (1336 : Fin 1536) ≤ ((6172811 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-164927301 / 9846784 : ℚ) : ℝ) - Real.exp ((-20669627 / 1230848 : ℚ) : ℝ)) ≤ ((6172811 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1336 : sigmaPower (1336 : Fin 1536) ≤ ((31222959147051 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1337 : sigmaFactor (1337 : Fin 1536) ≤ ((3169453 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-59866037 / 3579904 : ℚ) : ℝ) - Real.exp ((-120044529 / 7159808 : ℚ) : ℝ)) ≤ ((3169453 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1337 : sigmaPower (1337 : Fin 1536) ≤ ((7768326796397 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1338 : sigmaFactor (1338 : Fin 1536) ≤ ((13018849 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-219114775 / 13123584 : ℚ) : ℝ) - Real.exp ((-109843745 / 6561792 : ℚ) : ℝ)) ≤ ((13018849 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1338 : sigmaPower (1338 : Fin 1536) ≤ ((30923592946989 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1339 : sigmaFactor (1339 : Fin 1536) ≤ ((3342241 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-328081479 / 19681280 : ℚ) : ℝ) - Real.exp ((-1315761491 / 78725120 : ℚ) : ℝ)) ≤ ((3342241 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1339 : sigmaPower (1339 : Fin 1536) ≤ ((30773816392369 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1340 : sigmaFactor (1340 : Fin 1536) ≤ ((13728397 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-327491153 / 19677184 : ℚ) : ℝ) - Real.exp ((-82087467 / 4919296 : ℚ) : ℝ)) ≤ ((13728397 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1340 : sigmaPower (1340 : Fin 1536) ≤ ((15311988741407 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1341 : sigmaFactor (1341 : Fin 1536) ≤ ((14097393 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-217934123 / 13115392 : ℚ) : ℝ) - Real.exp ((-437012961 / 26230784 : ℚ) : ℝ)) ≤ ((14097393 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1341 : sigmaPower (1341 : Fin 1536) ≤ ((1904629761211 / 17592186044416 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1342 : sigmaFactor (1342 : Fin 1536) ≤ ((3619051 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-652623147 / 39337984 : ℚ) : ℝ) - Real.exp ((-327169931 / 19668992 : ℚ) : ℝ)) ≤ ((3619051 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1342 : sigmaPower (1342 : Fin 1536) ≤ ((30324112443075 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1343 : sigmaFactor (1343 : Fin 1536) ≤ ((232267 / 4398046511104 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-20357645 / 1229056 : ℚ) : ℝ) - Real.exp ((-1306321995 / 78659584 : ℚ) : ℝ)) ≤ ((232267 / 4398046511104 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1343 : sigmaPower (1343 : Fin 1536) ≤ ((7543521558725 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1344 : sigmaFactor (1344 : Fin 1536) ≤ ((7632155 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-6773613 / 409600 : ℚ) : ℝ) - Real.exp ((-106117 / 6400 : ℚ) : ℝ)) ≤ ((7632155 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1344 : sigmaPower (1344 : Fin 1536) ≤ ((7505999378951 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1345 : sigmaFactor (1345 : Fin 1536) ≤ ((7837071 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-649089771 / 39313408 : ℚ) : ℝ) - Real.exp ((-1301610827 / 78626816 : ℚ) : ℝ)) ≤ ((7837071 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1345 : sigmaPower (1345 : Fin 1536) ≤ ((14936923123355 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1346 : sigmaFactor (1346 : Fin 1536) ≤ ((8047431 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-647913409 / 39305216 : ℚ) : ℝ) - Real.exp ((-324814347 / 19652608 : ℚ) : ℝ)) ≤ ((8047431 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1346 : sigmaPower (1346 : Fin 1536) ≤ ((29723632388509 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1347 : sigmaFactor (1347 : Fin 1536) ≤ ((4131689 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-107789627 / 6549504 : ℚ) : ℝ) - Real.exp ((-432301793 / 26198016 : ℚ) : ℝ)) ≤ ((4131689 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1347 : sigmaPower (1347 : Fin 1536) ≤ ((14786677951029 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1348 : sigmaFactor (1348 : Fin 1536) ≤ ((16970119 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-29343765 / 1785856 : ℚ) : ℝ) - Real.exp ((-7355425 / 446464 : ℚ) : ℝ)) ≤ ((16970119 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1348 : sigmaPower (1348 : Fin 1536) ≤ ((29423016748181 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1349 : sigmaFactor (1349 : Fin 1536) ≤ ((4356313 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-644388613 / 39280640 : ℚ) : ℝ) - Real.exp ((-1292205651 / 78561280 : ℚ) : ℝ)) ≤ ((4356313 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1349 : sigmaPower (1349 : Fin 1536) ≤ ((29272614887671 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1350 : sigmaFactor (1350 : Fin 1536) ≤ ((8946231 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-12612061 / 770048 : ℚ) : ℝ) - Real.exp ((-6322833 / 385024 : ℚ) : ℝ)) ≤ ((8946231 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1350 : sigmaPower (1350 : Fin 1536) ≤ ((29122150281287 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1351 : sigmaFactor (1351 : Fin 1536) ≤ ((4593017 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-160510581 / 9816064 : ℚ) : ℝ) - Real.exp ((-1287511643 / 78528512 : ℚ) : ℝ)) ≤ ((4593017 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1351 : sigmaPower (1351 : Fin 1536) ≤ ((14485811444877 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1352 : sigmaFactor (1352 : Fin 1536) ≤ ((9432197 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-160217563 / 9814016 : ℚ) : ℝ) - Real.exp ((-20080731 / 1226752 : ℚ) : ℝ)) ≤ ((9432197 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1352 : sigmaPower (1352 : Fin 1536) ≤ ((3602629084221 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1353 : sigmaFactor (1353 : Fin 1536) ≤ ((19369775 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-213232965 / 13082624 : ℚ) : ℝ) - Real.exp ((-427607785 / 26165248 : ℚ) : ℝ)) ≤ ((19369775 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1353 : sigmaPower (1353 : Fin 1536) ≤ ((28670379593989 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1354 : sigmaFactor (1354 : Fin 1536) ≤ ((19888551 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-638528253 / 39239680 : ℚ) : ℝ) - Real.exp ((-320120339 / 19619840 : ℚ) : ℝ)) ≤ ((19888551 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1354 : sigmaPower (1354 : Fin 1536) ≤ ((28519663611045 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1355 : sigmaFactor (1355 : Fin 1536) ≤ ((20421075 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-318679163 / 19615744 : ℚ) : ℝ) - Real.exp ((-1278140787 / 78462976 : ℚ) : ℝ)) ≤ ((20421075 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1355 : sigmaPower (1355 : Fin 1536) ≤ ((7092221171383 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1356 : sigmaFactor (1356 : Fin 1536) ≤ ((20967707 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-106031519 / 6537216 : ℚ) : ℝ) - Real.exp ((-26579201 / 1634304 : ℚ) : ℝ)) ≤ ((20967707 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1356 : sigmaPower (1356 : Fin 1536) ≤ ((28218042778011 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1357 : sigmaFactor (1357 : Fin 1536) ≤ ((21528817 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-635020617 / 39215104 : ℚ) : ℝ) - Real.exp ((-1273463939 / 78430208 : ℚ) : ℝ)) ≤ ((21528817 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1357 : sigmaPower (1357 : Fin 1536) ≤ ((7016784462253 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1358 : sigmaFactor (1358 : Fin 1536) ≤ ((22104783 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-633852835 / 39206912 : ℚ) : ℝ) - Real.exp ((-317781915 / 19603456 : ℚ) : ℝ)) ≤ ((22104783 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1358 : sigmaPower (1358 : Fin 1536) ≤ ((3489521232379 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1359 : sigmaFactor (1359 : Fin 1536) ≤ ((11347997 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-2396537 / 148480 : ℚ) : ℝ) - Real.exp ((-38448267 / 2375680 : ℚ) : ℝ)) ≤ ((11347997 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1359 : sigmaPower (1359 : Fin 1536) ≤ ((27765138768533 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1360 : sigmaFactor (1360 : Fin 1536) ≤ ((11651425 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-78939927 / 4898816 : ℚ) : ℝ) - Real.exp ((-4947107 / 306176 : ℚ) : ℝ)) ≤ ((11651425 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1360 : sigmaPower (1360 : Fin 1536) ≤ ((27614044537947 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1361 : sigmaFactor (1361 : Fin 1536) ≤ ((23925759 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-630353779 / 39182336 : ℚ) : ℝ) - Real.exp ((-1264127403 / 78364672 : ℚ) : ℝ)) ≤ ((23925759 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1361 : sigmaPower (1361 : Fin 1536) ≤ ((27462887127669 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1362 : sigmaFactor (1362 : Fin 1536) ≤ ((12282571 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-209729619 / 13058048 : ℚ) : ℝ) - Real.exp ((-105149737 / 6529024 : ℚ) : ℝ)) ≤ ((12282571 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1362 : sigmaPower (1362 : Fin 1536) ≤ ((27311666498065 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1363 : sigmaFactor (1363 : Fin 1536) ≤ ((12610715 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-314012325 / 19582976 : ℚ) : ℝ) - Real.exp ((-1259467715 / 78331904 : ℚ) : ℝ)) ≤ ((12610715 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1363 : sigmaPower (1363 : Fin 1536) ≤ ((27160382609465 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1364 : sigmaFactor (1364 : Fin 1536) ≤ ((3236883 / 35184372088832 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-313430579 / 19578880 : ℚ) : ℝ) - Real.exp ((-78571251 / 4894720 : ℚ) : ℝ)) ≤ ((3236883 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1364 : sigmaPower (1364 : Fin 1536) ≤ ((27009035422167 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1365 : sigmaFactor (1365 : Fin 1536) ≤ ((26586497 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-208566127 / 13049856 : ℚ) : ℝ) - Real.exp ((-418271249 / 26099712 : ℚ) : ℝ)) ≤ ((26586497 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1365 : sigmaPower (1365 : Fin 1536) ≤ ((26857624896435 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1366 : sigmaFactor (1366 : Fin 1536) ≤ ((6824049 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-624536319 / 39141376 : ℚ) : ℝ) - Real.exp ((-313122227 / 19570688 : ℚ) : ℝ)) ≤ ((6824049 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1366 : sigmaPower (1366 : Fin 1536) ≤ ((6676537748125 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1367 : sigmaFactor (1367 : Fin 1536) ≤ ((7006159 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-9167279 / 575488 : ℚ) : ℝ) - Real.exp ((-73539147 / 4603904 : ℚ) : ℝ)) ≤ ((7006159 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1367 : sigmaPower (1367 : Fin 1536) ≤ ((26554613670561 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1368 : sigmaFactor (1368 : Fin 1536) ≤ ((28772307 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-51851195 / 3260416 : ℚ) : ℝ) - Real.exp ((-6499185 / 407552 : ℚ) : ℝ)) ≤ ((28772307 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1368 : sigmaPower (1368 : Fin 1536) ≤ ((13201506445391 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1369 : sigmaFactor (1369 : Fin 1536) ≤ ((29539711 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-621054423 / 39116800 : ℚ) : ℝ) - Real.exp ((-1245522971 / 78233600 : ℚ) : ℝ)) ≤ ((29539711 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1369 : sigmaPower (1369 : Fin 1536) ≤ ((13125674306647 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1370 : sigmaFactor (1370 : Fin 1536) ≤ ((30327363 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-56354111 / 3555328 : ℚ) : ℝ) - Real.exp ((-28254633 / 1777664 : ℚ) : ℝ)) ≤ ((30327363 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1370 : sigmaPower (1370 : Fin 1536) ≤ ((6524905199549 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1371 : sigmaFactor (1371 : Fin 1536) ≤ ((31135791 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-103122789 / 6516736 : ℚ) : ℝ) - Real.exp ((-413628721 / 26066944 : ℚ) : ℝ)) ≤ ((31135791 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1371 : sigmaPower (1371 : Fin 1536) ≤ ((12973914702775 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1372 : sigmaFactor (1372 : Fin 1536) ≤ ((998923 / 8796093022208 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-308789481 / 19546112 : ℚ) : ℝ) - Real.exp ((-77410619 / 4886528 : ℚ) : ℝ)) ≤ ((998923 / 8796093022208 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1372 : sigmaPower (1372 : Fin 1536) ≤ ((25795974395389 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1373 : sigmaFactor (1373 : Fin 1536) ≤ ((8204289 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-616421905 / 39084032 : ℚ) : ℝ) - Real.exp ((-1236255075 / 78168064 : ℚ) : ℝ)) ≤ ((8204289 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1373 : sigmaPower (1373 : Fin 1536) ≤ ((25644055727709 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1374 : sigmaFactor (1374 : Fin 1536) ≤ ((33691219 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-205088521 / 13025280 : ℚ) : ℝ) - Real.exp ((-102828473 / 6512640 : ℚ) : ℝ)) ≤ ((33691219 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1374 : sigmaPower (1374 : Fin 1536) ≤ ((25492073362475 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1375 : sigmaFactor (1375 : Fin 1536) ≤ ((17294155 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-38381871 / 2441728 : ℚ) : ℝ) - Real.exp ((-1231629707 / 78135296 : ℚ) : ℝ)) ≤ ((17294155 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1375 : sigmaPower (1375 : Fin 1536) ≤ ((791875851863 / 8796093022208 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1376 : sigmaFactor (1376 : Fin 1536) ≤ ((35509029 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-38309689 / 2441216 : ℚ) : ℝ) - Real.exp ((-1200507 / 76288 : ℚ) : ℝ)) ≤ ((35509029 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1376 : sigmaPower (1376 : Fin 1536) ≤ ((12593958689515 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1377 : sigmaFactor (1377 : Fin 1536) ≤ ((4556749 / 35184372088832 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-203933609 / 13017088 : ℚ) : ℝ) - Real.exp ((-409003353 / 26034176 : ℚ) : ℝ)) ≤ ((4556749 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1377 : sigmaPower (1377 : Fin 1536) ≤ ((25035743680579 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1378 : sigmaFactor (1378 : Fin 1536) ≤ ((37423829 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-610647345 / 39043072 : ℚ) : ℝ) - Real.exp ((-306175595 / 19521536 : ℚ) : ℝ)) ≤ ((37423829 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1378 : sigmaPower (1378 : Fin 1536) ≤ ((24883506124093 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1379 : sigmaFactor (1379 : Fin 1536) ≤ ((9604797 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-304747289 / 19517440 : ℚ) : ℝ) - Real.exp ((-1222396131 / 78069760 : ℚ) : ℝ)) ≤ ((9604797 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1379 : sigmaPower (1379 : Fin 1536) ≤ ((12365602334683 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1380 : sigmaFactor (1380 : Fin 1536) ≤ ((9860183 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-101390421 / 6504448 : ℚ) : ℝ) - Real.exp ((-25418569 / 1626112 : ℚ) : ℝ)) ≤ ((9860183 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1380 : sigmaPower (1380 : Fin 1536) ≤ ((12289419638081 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1381 : sigmaFactor (1381 : Fin 1536) ≤ ((40489143 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-55199199 / 3547136 : ℚ) : ℝ) - Real.exp ((-110707993 / 7094272 : ℚ) : ℝ)) ≤ ((40489143 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1381 : sigmaPower (1381 : Fin 1536) ≤ ((24426409904207 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1382 : sigmaFactor (1382 : Fin 1536) ≤ ((41565119 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-606040567 / 39010304 : ℚ) : ℝ) - Real.exp ((-303871491 / 19505152 : ℚ) : ℝ)) ≤ ((41565119 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1382 : sigmaPower (1382 : Fin 1536) ≤ ((24273916513197 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1383 : sigmaFactor (1383 : Fin 1536) ≤ ((666709 / 4398046511104 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-50407555 / 3250176 : ℚ) : ℝ) - Real.exp ((-404395145 / 26001408 : ℚ) : ℝ)) ≤ ((666709 / 4398046511104 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1383 : sigmaPower (1383 : Fin 1536) ≤ ((24121359062791 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1384 : sigmaFactor (1384 : Fin 1536) ≤ ((43802649 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-8878551 / 573440 : ℚ) : ℝ) - Real.exp ((-1112947 / 71680 : ℚ) : ℝ)) ≤ ((43802649 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1384 : sigmaPower (1384 : Fin 1536) ≤ ((23968737512617 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1385 : sigmaFactor (1385 : Fin 1536) ≤ ((11241423 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-602592991 / 38985728 : ℚ) : ℝ) - Real.exp ((-1208588667 / 77971456 : ℚ) : ℝ)) ≤ ((11241423 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1385 : sigmaPower (1385 : Fin 1536) ≤ ((23816051822265 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1386 : sigmaFactor (1386 : Fin 1536) ≤ ((23079639 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-200481743 / 12992512 : ℚ) : ℝ) - Real.exp ((-100524369 / 6496256 : ℚ) : ℝ)) ≤ ((23079639 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1386 : sigmaPower (1386 : Fin 1536) ≤ ((369739092989 / 4398046511104 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1387 : sigmaFactor (1387 : Fin 1536) ≤ ((47384199 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-300149091 / 19484672 : ℚ) : ℝ) - Real.exp ((-1203997619 / 77938688 : ℚ) : ℝ)) ≤ ((47384199 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1387 : sigmaPower (1387 : Fin 1536) ≤ ((23510487859233 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1388 : sigmaFactor (1388 : Fin 1536) ≤ ((12160317 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-299575925 / 19480576 : ℚ) : ℝ) - Real.exp ((-75106515 / 4870144 : ℚ) : ℝ)) ≤ ((12160317 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1388 : sigmaPower (1388 : Fin 1536) ≤ ((23357609505567 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1389 : sigmaFactor (1389 : Fin 1536) ≤ ((49931321 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-199335411 / 12984320 : ℚ) : ℝ) - Real.exp ((-399804097 / 25968640 : ℚ) : ℝ)) ≤ ((49931321 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1389 : sigmaPower (1389 : Fin 1536) ≤ ((11602333424877 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1390 : sigmaFactor (1390 : Fin 1536) ≤ ((51255211 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-596861331 / 38944768 : ℚ) : ℝ) - Real.exp ((-299280443 / 19472384 : ℚ) : ℝ)) ≤ ((51255211 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1390 : sigmaPower (1390 : Fin 1536) ≤ ((23051659851217 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1391 : sigmaFactor (1391 : Fin 1536) ≤ ((6576727 / 35184372088832 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-74464643 / 4867072 : ℚ) : ℝ) - Real.exp ((-1194832683 / 77873152 : ℚ) : ℝ)) ≤ ((6576727 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1391 : sigmaPower (1391 : Fin 1536) ≤ ((22898588469343 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1392 : sigmaFactor (1392 : Fin 1536) ≤ ((13502009 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-2252173 / 147456 : ℚ) : ℝ) - Real.exp ((-141163 / 9216 : ℚ) : ℝ)) ≤ ((13502009 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1392 : sigmaPower (1392 : Fin 1536) ≤ ((355397697867 / 4398046511104 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1393 : sigmaFactor (1393 : Fin 1536) ≤ ((27719397 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-593430915 / 38920192 : ℚ) : ℝ) - Real.exp ((-1190258795 / 77840384 : ℚ) : ℝ)) ≤ ((27719397 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1393 : sigmaPower (1393 : Fin 1536) ≤ ((11296126196485 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1394 : sigmaFactor (1394 : Fin 1536) ≤ ((56907035 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-592288873 / 38912000 : ℚ) : ℝ) - Real.exp ((-296993499 / 19456000 : ℚ) : ℝ)) ≤ ((56907035 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1394 : sigmaPower (1394 : Fin 1536) ≤ ((22438987617075 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1395 : sigmaFactor (1395 : Fin 1536) ≤ ((58413731 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-98524591 / 6483968 : ℚ) : ℝ) - Real.exp ((-395230209 / 25935872 : ℚ) : ℝ)) ≤ ((58413731 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1395 : sigmaPower (1395 : Fin 1536) ≤ ((22285658295053 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1396 : sigmaFactor (1396 : Fin 1536) ≤ ((14989969 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-295003467 / 19447808 : ℚ) : ℝ) - Real.exp ((-73963043 / 4861952 : ℚ) : ℝ)) ≤ ((14989969 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1396 : sigmaPower (1396 : Fin 1536) ≤ ((22132264386123 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1397 : sigmaFactor (1397 : Fin 1536) ≤ ((15386623 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-588867037 / 38887424 : ℚ) : ℝ) - Real.exp ((-1181128179 / 77774848 : ℚ) : ℝ)) ≤ ((15386623 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1397 : sigmaPower (1397 : Fin 1536) ≤ ((21978805849467 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1398 : sigmaFactor (1398 : Fin 1536) ≤ ((31587313 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-195909285 / 12959744 : ℚ) : ℝ) - Real.exp ((-98237425 / 6479872 : ℚ) : ℝ)) ≤ ((31587313 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1398 : sigmaPower (1398 : Fin 1536) ≤ ((2728160330529 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1399 : sigmaFactor (1399 : Fin 1536) ≤ ((64845351 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-146647347 / 9717760 : ℚ) : ℝ) - Real.exp ((-1176571451 / 77742080 : ℚ) : ℝ)) ≤ ((64845351 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1399 : sigmaPower (1399 : Fin 1536) ≤ ((5417923682383 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1400 : sigmaFactor (1400 : Fin 1536) ≤ ((66559767 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-146362909 / 9715712 : ℚ) : ℝ) - Real.exp ((-18348363 / 1214464 : ℚ) : ℝ)) ≤ ((66559767 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1400 : sigmaPower (1400 : Fin 1536) ≤ ((10759021032223 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1401 : sigmaFactor (1401 : Fin 1536) ≤ ((68319005 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-11457149 / 761856 : ℚ) : ℝ) - Real.exp ((-22980793 / 1523712 : ℚ) : ℝ)) ≤ ((68319005 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1401 : sigmaPower (1401 : Fin 1536) ≤ ((5341081152005 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1402 : sigmaFactor (1402 : Fin 1536) ≤ ((35062111 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-583178277 / 38846464 : ℚ) : ℝ) - Real.exp ((-292436771 / 19423232 : ℚ) : ℝ)) ≤ ((35062111 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1402 : sigmaPower (1402 : Fin 1536) ≤ ((21210542319263 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1403 : sigmaFactor (1403 : Fin 1536) ≤ ((35988303 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-26456485 / 1765376 : ℚ) : ℝ) - Real.exp ((-106134105 / 7061504 : ℚ) : ℝ)) ≤ ((35988303 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1403 : sigmaPower (1403 : Fin 1536) ≤ ((10528347578575 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1404 : sigmaFactor (1404 : Fin 1536) ≤ ((36938687 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-96817963 / 6471680 : ℚ) : ℝ) - Real.exp ((-24275097 / 1617920 : ℚ) : ℝ)) ≤ ((36938687 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1404 : sigmaPower (1404 : Fin 1536) ≤ ((20902783080623 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1405 : sigmaFactor (1405 : Fin 1536) ≤ ((1184809 / 4398046511104 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-579773601 / 38821888 : ℚ) : ℝ) - Real.exp ((-1162935587 / 77643776 : ℚ) : ℝ)) ≤ ((1184809 / 4398046511104 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1405 : sigmaPower (1405 : Fin 1536) ≤ ((5187201512147 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1406 : sigmaFactor (1406 : Fin 1536) ≤ ((77829091 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-578640139 / 38813696 : ℚ) : ℝ) - Real.exp ((-290166987 / 19406848 : ℚ) : ℝ)) ≤ ((77829091 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1406 : sigmaPower (1406 : Fin 1536) ≤ ((5148691004979 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1407 : sigmaFactor (1407 : Fin 1536) ≤ ((39941317 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1931 / 100 : ℚ) : ℝ) * (Real.exp ((-3007851 / 202112 : ℚ) : ℝ) - Real.exp ((-386133913 / 25870336 : ℚ) : ℝ)) ≤ ((39941317 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1407 : sigmaPower (1407 : Fin 1536) ≤ ((20440656953445 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

end LegendreK6.M2Pilot.Enclosures.Sigma010
