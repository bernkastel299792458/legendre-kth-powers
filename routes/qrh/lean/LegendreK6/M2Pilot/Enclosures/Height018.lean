import LegendreK6.M2PilotDefinitions
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp

/-! Generated proposals: every bound is checked by Lean, not by trusting Arb. -/
namespace LegendreK6.M2Pilot.Enclosures.Height018
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem height_z_bounds_2417 : ((137951995001907 / 2305843009213693952 : ℚ) : ℝ) ≤ heightZ ((2417 / 64 : ℚ) : ℝ) ∧
    heightZ ((2417 / 64 : ℚ) : ℝ) ≤ ((1103615960015259 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((137951995001907 / 2305843009213693952 : ℚ) : ℝ) ≤ Real.exp (-((2417 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1523 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2417 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1523 / 192 : ℚ) : ℝ) ≤ ((1103615960015259 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2417 : ((17039016187 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2417 / 64 : ℚ) : ℝ) ∧
    logKernel ((2417 / 64 : ℚ) : ℝ) ≤ ((34078032379 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2417
  constructor
  · exact (show ((17039016187 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((137951995001907 / 2305843009213693952 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2417 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1103615960015259 / 18446744073709551616 : ℚ) : ℝ) ≤ ((34078032379 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2418 : ((543252990228661 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((1209 / 32 : ℚ) : ℝ) ∧
    heightZ ((1209 / 32 : ℚ) : ℝ) ≤ ((1086505980457325 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((543252990228661 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((1209 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-763 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1209 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-763 / 96 : ℚ) : ℝ) ≤ ((1086505980457325 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2418 : ((16514780771 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((1209 / 32 : ℚ) : ℝ) ∧
    logKernel ((1209 / 32 : ℚ) : ℝ) ≤ ((33029561547 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2418
  constructor
  · exact (show ((16514780771 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((543252990228661 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1209 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1086505980457325 / 18446744073709551616 : ℚ) : ℝ) ≤ ((33029561547 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2419 : ((534830633272651 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2419 / 64 : ℚ) : ℝ) ∧
    heightZ ((2419 / 64 : ℚ) : ℝ) ≤ ((1069661266545305 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((534830633272651 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2419 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1529 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2419 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1529 / 192 : ℚ) : ℝ) ≤ ((1069661266545305 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2419 : ((32013348767 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2419 / 64 : ℚ) : ℝ) ∧
    logKernel ((2419 / 64 : ℚ) : ℝ) ≤ ((8003337193 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2419
  constructor
  · exact (show ((32013348767 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((534830633272651 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2419 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1069661266545305 / 18446744073709551616 : ℚ) : ℝ) ≤ ((8003337193 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2420 : ((526538852858271 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((605 / 16 : ℚ) : ℝ) ∧
    heightZ ((605 / 16 : ℚ) : ℝ) ≤ ((1053077705716545 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((526538852858271 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((605 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-383 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((605 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-383 / 48 : ℚ) : ℝ) ≤ ((1053077705716545 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2420 : ((7757100393 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((605 / 16 : ℚ) : ℝ) ∧
    logKernel ((605 / 16 : ℚ) : ℝ) ≤ ((31028401577 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2420
  constructor
  · exact (show ((7757100393 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((526538852858271 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((605 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1053077705716545 / 18446744073709551616 : ℚ) : ℝ) ≤ ((31028401577 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2421 : ((518375624583883 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2421 / 64 : ℚ) : ℝ) ∧
    heightZ ((2421 / 64 : ℚ) : ℝ) ≤ ((1036751249167769 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((518375624583883 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2421 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1535 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2421 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1535 / 192 : ℚ) : ℝ) ≤ ((1036751249167769 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2421 : ((469902469 / 1125899906842624 : ℚ) : ℝ) ≤ logKernel ((2421 / 64 : ℚ) : ℝ) ∧
    logKernel ((2421 / 64 : ℚ) : ℝ) ≤ ((30073758021 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2421
  constructor
  · exact (show ((469902469 / 1125899906842624 : ℚ) : ℝ) ≤ zKernel ((518375624583883 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2421 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1036751249167769 / 18446744073709551616 : ℚ) : ℝ) ≤ ((30073758021 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2422 : ((255169477716643 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((1211 / 32 : ℚ) : ℝ) ∧
    heightZ ((1211 / 32 : ℚ) : ℝ) ≤ ((1020677910866575 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((255169477716643 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((1211 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-769 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1211 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-769 / 96 : ℚ) : ℝ) ≤ ((1020677910866575 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2422 : ((14574242877 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((1211 / 32 : ℚ) : ℝ) ∧
    logKernel ((1211 / 32 : ℚ) : ℝ) ≤ ((29148485759 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2422
  constructor
  · exact (show ((14574242877 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((255169477716643 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1211 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1020677910866575 / 18446744073709551616 : ℚ) : ℝ) ≤ ((29148485759 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2423 : ((125606720822283 / 2305843009213693952 : ℚ) : ℝ) ≤ heightZ ((2423 / 64 : ℚ) : ℝ) ∧
    heightZ ((2423 / 64 : ℚ) : ℝ) ≤ ((1004853766578267 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((125606720822283 / 2305843009213693952 : ℚ) : ℝ) ≤ Real.exp (-((2423 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1541 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2423 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1541 / 192 : ℚ) : ℝ) ≤ ((1004853766578267 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2423 : ((3531460141 / 9007199254740992 : ℚ) : ℝ) ≤ logKernel ((2423 / 64 : ℚ) : ℝ) ∧
    logKernel ((2423 / 64 : ℚ) : ℝ) ≤ ((28251681133 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2423
  constructor
  · exact (show ((3531460141 / 9007199254740992 : ℚ) : ℝ) ≤ zKernel ((125606720822283 / 2305843009213693952 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2423 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1004853766578267 / 18446744073709551616 : ℚ) : ℝ) ≤ ((28251681133 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2424 : ((989274952907765 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((303 / 8 : ℚ) : ℝ) ∧
    heightZ ((303 / 8 : ℚ) : ℝ) ≤ ((123659369113471 / 2305843009213693952 : ℚ) : ℝ) := by
  have h : ((989274952907765 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((303 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-193 / 24 : ℚ) : ℝ) ∧
      Real.exp (-((303 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-193 / 24 : ℚ) : ℝ) ≤ ((123659369113471 / 2305843009213693952 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2424 : ((27382468279 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((303 / 8 : ℚ) : ℝ) ∧
    logKernel ((303 / 8 : ℚ) : ℝ) ≤ ((6845617071 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2424
  constructor
  · exact (show ((27382468279 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((989274952907765 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((303 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((123659369113471 / 2305843009213693952 : ℚ) : ℝ) ≤ ((6845617071 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2425 : ((243484416589097 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((2425 / 64 : ℚ) : ℝ) ∧
    heightZ ((2425 / 64 : ℚ) : ℝ) ≤ ((973937666356391 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((243484416589097 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((2425 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1547 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2425 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1547 / 192 : ℚ) : ℝ) ≤ ((973937666356391 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2425 : ((13269999149 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2425 / 64 : ℚ) : ℝ) ∧
    logKernel ((2425 / 64 : ℚ) : ℝ) ≤ ((26539998303 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2425
  constructor
  · exact (show ((13269999149 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((243484416589097 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2425 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((973937666356391 / 18446744073709551616 : ℚ) : ℝ) ≤ ((26539998303 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2426 : ((479419081196613 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((1213 / 32 : ℚ) : ℝ) ∧
    heightZ ((1213 / 32 : ℚ) : ℝ) ≤ ((958838162393229 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((479419081196613 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((1213 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-775 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1213 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-775 / 96 : ℚ) : ℝ) ≤ ((958838162393229 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2426 : ((25723448393 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1213 / 32 : ℚ) : ℝ) ∧
    logKernel ((1213 / 32 : ℚ) : ℝ) ≤ ((12861724199 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2426
  constructor
  · exact (show ((25723448393 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((479419081196613 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1213 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((958838162393229 / 18446744073709551616 : ℚ) : ℝ) ≤ ((12861724199 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2427 : ((58998297158809 / 1152921504606846976 : ℚ) : ℝ) ≤ heightZ ((2427 / 64 : ℚ) : ℝ) ∧
    heightZ ((2427 / 64 : ℚ) : ℝ) ≤ ((943972754540947 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((58998297158809 / 1152921504606846976 : ℚ) : ℝ) ≤ Real.exp (-((2427 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1553 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2427 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1553 / 192 : ℚ) : ℝ) ≤ ((943972754540947 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2427 : ((779125659 / 2251799813685248 : ℚ) : ℝ) ≤ logKernel ((2427 / 64 : ℚ) : ℝ) ∧
    logKernel ((2427 / 64 : ℚ) : ℝ) ≤ ((24932021093 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2427
  constructor
  · exact (show ((779125659 / 2251799813685248 : ℚ) : ℝ) ≤ zKernel ((58998297158809 / 1152921504606846976 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2427 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((943972754540947 / 18446744073709551616 : ℚ) : ℝ) ≤ ((24932021093 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2428 : ((232334453368935 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((607 / 16 : ℚ) : ℝ) ∧
    heightZ ((607 / 16 : ℚ) : ℝ) ≤ ((929337813475743 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((232334453368935 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((607 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-389 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((607 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-389 / 48 : ℚ) : ℝ) ≤ ((929337813475743 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2428 : ((24164943441 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((607 / 16 : ℚ) : ℝ) ∧
    logKernel ((607 / 16 : ℚ) : ℝ) ≤ ((12082471723 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2428
  constructor
  · exact (show ((24164943441 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((232334453368935 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((607 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((929337813475743 / 18446744073709551616 : ℚ) : ℝ) ≤ ((12082471723 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2429 : ((914929766141263 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2429 / 64 : ℚ) : ℝ) ∧
    heightZ ((2429 / 64 : ℚ) : ℝ) ≤ ((457464883070633 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((914929766141263 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2429 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1559 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2429 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1559 / 192 : ℚ) : ℝ) ≤ ((457464883070633 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2429 : ((5855366573 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((2429 / 64 : ℚ) : ℝ) ∧
    logKernel ((2429 / 64 : ℚ) : ℝ) ≤ ((23421466297 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2429
  constructor
  · exact (show ((5855366573 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((914929766141263 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2429 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((457464883070633 / 9223372036854775808 : ℚ) : ℝ) ≤ ((23421466297 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2430 : ((900745094876265 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1215 / 32 : ℚ) : ℝ) ∧
    heightZ ((1215 / 32 : ℚ) : ℝ) ≤ ((225186273719067 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((900745094876265 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1215 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-781 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1215 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-781 / 96 : ℚ) : ℝ) ≤ ((225186273719067 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2430 : ((11350431765 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((1215 / 32 : ℚ) : ℝ) ∧
    logKernel ((1215 / 32 : ℚ) : ℝ) ≤ ((22700863535 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2430
  constructor
  · exact (show ((11350431765 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((900745094876265 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1215 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((225186273719067 / 4611686018427387904 : ℚ) : ℝ) ≤ ((22700863535 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2431 : ((886780336555781 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2431 / 64 : ℚ) : ℝ) ∧
    heightZ ((2431 / 64 : ℚ) : ℝ) ≤ ((110847542069473 / 2305843009213693952 : ℚ) : ℝ) := by
  have h : ((886780336555781 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2431 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1565 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2431 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1565 / 192 : ℚ) : ℝ) ≤ ((110847542069473 / 2305843009213693952 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2431 : ((22002431385 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2431 / 64 : ℚ) : ℝ) ∧
    logKernel ((2431 / 64 : ℚ) : ℝ) ≤ ((11001215695 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2431
  constructor
  · exact (show ((22002431385 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((886780336555781 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2431 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((110847542069473 / 2305843009213693952 : ℚ) : ℝ) ≤ ((11001215695 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2432 : ((109129010218203 / 2305843009213693952 : ℚ) : ℝ) ≤ heightZ ((38 / 1 : ℚ) : ℝ) ∧
    heightZ ((38 / 1 : ℚ) : ℝ) ≤ ((873032081745627 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((109129010218203 / 2305843009213693952 : ℚ) : ℝ) ≤ Real.exp (-((38 / 1 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-49 / 6 : ℚ) : ℝ) ∧
      Real.exp (-((38 / 1 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-49 / 6 : ℚ) : ℝ) ≤ ((873032081745627 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2432 : ((21325487737 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((38 / 1 : ℚ) : ℝ) ∧
    logKernel ((38 / 1 : ℚ) : ℝ) ≤ ((10662743871 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2432
  constructor
  · exact (show ((21325487737 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((109129010218203 / 2305843009213693952 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((38 / 1 : ℚ) : ℝ)) hh).trans
      (show zKernel ((873032081745627 / 18446744073709551616 : ℚ) : ℝ) ≤ ((10662743871 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2433 : ((859496973869981 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2433 / 64 : ℚ) : ℝ) ∧
    heightZ ((2433 / 64 : ℚ) : ℝ) ≤ ((26859280433437 / 576460752303423488 : ℚ) : ℝ) := by
  have h : ((859496973869981 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2433 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1571 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2433 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1571 / 192 : ℚ) : ℝ) ≤ ((26859280433437 / 576460752303423488 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2433 : ((322958929 / 1125899906842624 : ℚ) : ℝ) ≤ logKernel ((2433 / 64 : ℚ) : ℝ) ∧
    logKernel ((2433 / 64 : ℚ) : ℝ) ≤ ((20669371461 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2433
  constructor
  · exact (show ((322958929 / 1125899906842624 : ℚ) : ℝ) ≤ zKernel ((859496973869981 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2433 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((26859280433437 / 576460752303423488 : ℚ) : ℝ) ≤ ((20669371461 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2434 : ((846171708391927 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1217 / 32 : ℚ) : ℝ) ∧
    heightZ ((1217 / 32 : ℚ) : ℝ) ≤ ((423085854195965 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((846171708391927 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1217 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-787 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1217 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-787 / 96 : ℚ) : ℝ) ≤ ((423085854195965 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2434 : ((20033441751 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1217 / 32 : ℚ) : ℝ) ∧
    logKernel ((1217 / 32 : ℚ) : ℝ) ≤ ((5008360439 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2434
  constructor
  · exact (show ((20033441751 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((846171708391927 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1217 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((423085854195965 / 9223372036854775808 : ℚ) : ℝ) ≤ ((5008360439 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2435 : ((833053032006631 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2435 / 64 : ℚ) : ℝ) ∧
    heightZ ((2435 / 64 : ℚ) : ℝ) ≤ ((416526516003317 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((833053032006631 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2435 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1577 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2435 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1577 / 192 : ℚ) : ℝ) ≤ ((416526516003317 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2435 : ((9708538773 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2435 / 64 : ℚ) : ℝ) ∧
    logKernel ((2435 / 64 : ℚ) : ℝ) ≤ ((19417077551 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2435
  constructor
  · exact (show ((9708538773 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((833053032006631 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2435 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((416526516003317 / 9223372036854775808 : ℚ) : ℝ) ≤ ((19417077551 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2436 : ((820137741847081 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((609 / 16 : ℚ) : ℝ) ∧
    heightZ ((609 / 16 : ℚ) : ℝ) ≤ ((205034435461771 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((820137741847081 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((609 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-395 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((609 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-395 / 48 : ℚ) : ℝ) ≤ ((205034435461771 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2436 : ((9409838437 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((609 / 16 : ℚ) : ℝ) ∧
    logKernel ((609 / 16 : ℚ) : ℝ) ≤ ((18819676879 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2436
  constructor
  · exact (show ((9409838437 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((820137741847081 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((609 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((205034435461771 / 4611686018427387904 : ℚ) : ℝ) ≤ ((18819676879 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2437 : ((807422684702113 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2437 / 64 : ℚ) : ℝ) ∧
    heightZ ((2437 / 64 : ℚ) : ℝ) ≤ ((201855671175529 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((807422684702113 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2437 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1583 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2437 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1583 / 192 : ℚ) : ℝ) ≤ ((201855671175529 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2437 : ((570020509 / 2251799813685248 : ℚ) : ℝ) ≤ logKernel ((2437 / 64 : ℚ) : ℝ) ∧
    logKernel ((2437 / 64 : ℚ) : ℝ) ≤ ((18240656293 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2437
  constructor
  · exact (show ((570020509 / 2251799813685248 : ℚ) : ℝ) ≤ zKernel ((807422684702113 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2437 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((201855671175529 / 4611686018427387904 : ℚ) : ℝ) ≤ ((18240656293 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2438 : ((794904756246571 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1219 / 32 : ℚ) : ℝ) ∧
    heightZ ((1219 / 32 : ℚ) : ℝ) ≤ ((397452378123287 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((794904756246571 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1219 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-793 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1219 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-793 / 96 : ℚ) : ℝ) ≤ ((397452378123287 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2438 : ((17679450293 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1219 / 32 : ℚ) : ℝ) ∧
    logKernel ((1219 / 32 : ℚ) : ℝ) ≤ ((8839725149 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2438
  constructor
  · exact (show ((17679450293 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((794904756246571 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1219 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((397452378123287 / 9223372036854775808 : ℚ) : ℝ) ≤ ((8839725149 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2439 : ((391290450141701 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2439 / 64 : ℚ) : ℝ) ∧
    heightZ ((2439 / 64 : ℚ) : ℝ) ≤ ((782580900283405 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((391290450141701 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2439 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1589 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2439 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1589 / 192 : ℚ) : ℝ) ≤ ((782580900283405 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2439 : ((17135510791 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2439 / 64 : ℚ) : ℝ) ∧
    logKernel ((2439 / 64 : ℚ) : ℝ) ≤ ((4283877699 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2439
  constructor
  · exact (show ((17135510791 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((391290450141701 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2439 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((782580900283405 / 18446744073709551616 : ℚ) : ℝ) ≤ ((4283877699 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2440 : ((385224053998747 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((305 / 8 : ℚ) : ℝ) ∧
    heightZ ((305 / 8 : ℚ) : ℝ) ≤ ((770448107997497 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((385224053998747 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((305 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-199 / 24 : ℚ) : ℝ) ∧
      Real.exp (-((305 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-199 / 24 : ℚ) : ℝ) ≤ ((770448107997497 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2440 : ((16608306549 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((305 / 8 : ℚ) : ℝ) ∧
    logKernel ((305 / 8 : ℚ) : ℝ) ≤ ((8304153277 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2440
  constructor
  · exact (show ((16608306549 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((385224053998747 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((305 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((770448107997497 / 18446744073709551616 : ℚ) : ℝ) ≤ ((8304153277 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2441 : ((758503417221091 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2441 / 64 : ℚ) : ℝ) ∧
    heightZ ((2441 / 64 : ℚ) : ℝ) ≤ ((379251708610547 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((758503417221091 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2441 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1595 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2441 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1595 / 192 : ℚ) : ℝ) ≤ ((379251708610547 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2441 : ((16097322675 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2441 / 64 : ℚ) : ℝ) ∧
    logKernel ((2441 / 64 : ℚ) : ℝ) ≤ ((2012165335 / 9007199254740992 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2441
  constructor
  · exact (show ((16097322675 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((758503417221091 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2441 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((379251708610547 / 9223372036854775808 : ℚ) : ℝ) ≤ ((2012165335 / 9007199254740992 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2442 : ((746743911710591 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1221 / 32 : ℚ) : ℝ) ∧
    heightZ ((1221 / 32 : ℚ) : ℝ) ≤ ((373371955855297 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((746743911710591 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1221 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-799 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1221 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-799 / 96 : ℚ) : ℝ) ≤ ((373371955855297 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2442 : ((15602060123 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1221 / 32 : ℚ) : ℝ) ∧
    logKernel ((1221 / 32 : ℚ) : ℝ) ≤ ((487564379 / 2251799813685248 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2442
  constructor
  · exact (show ((15602060123 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((746743911710591 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1221 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((373371955855297 / 9223372036854775808 : ℚ) : ℝ) ≤ ((487564379 / 2251799813685248 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2443 : ((367583360217279 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2443 / 64 : ℚ) : ℝ) ∧
    heightZ ((2443 / 64 : ℚ) : ℝ) ≤ ((735166720434561 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((367583360217279 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2443 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1601 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2443 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1601 / 192 : ℚ) : ℝ) ≤ ((735166720434561 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2443 : ((15122035197 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2443 / 64 : ℚ) : ℝ) ∧
    logKernel ((2443 / 64 : ℚ) : ℝ) ≤ ((7561017601 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2443
  constructor
  · exact (show ((15122035197 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((367583360217279 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2443 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((735166720434561 / 18446744073709551616 : ℚ) : ℝ) ≤ ((7561017601 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2444 : ((723769016872773 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((611 / 16 : ℚ) : ℝ) ∧
    heightZ ((611 / 16 : ℚ) : ℝ) ≤ ((90471127109097 / 2305843009213693952 : ℚ) : ℝ) := by
  have h : ((723769016872773 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((611 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-401 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((611 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-401 / 48 : ℚ) : ℝ) ≤ ((90471127109097 / 2305843009213693952 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2444 : ((7328389543 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((611 / 16 : ℚ) : ℝ) ∧
    logKernel ((611 / 16 : ℚ) : ℝ) ≤ ((14656779091 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2444
  constructor
  · exact (show ((7328389543 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((723769016872773 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((611 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((90471127109097 / 2305843009213693952 : ℚ) : ℝ) ≤ ((14656779091 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2445 : ((712548018326153 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2445 / 64 : ℚ) : ℝ) ∧
    heightZ ((2445 / 64 : ℚ) : ℝ) ≤ ((178137004581539 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((712548018326153 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2445 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1607 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2445 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1607 / 192 : ℚ) : ℝ) ≤ ((178137004581539 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2445 : ((14205837401 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2445 / 64 : ℚ) : ℝ) ∧
    logKernel ((2445 / 64 : ℚ) : ℝ) ≤ ((7102918703 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2445
  constructor
  · exact (show ((14205837401 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((712548018326153 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2445 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((178137004581539 / 4611686018427387904 : ℚ) : ℝ) ≤ ((7102918703 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2446 : ((350750492618681 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((1223 / 32 : ℚ) : ℝ) ∧
    heightZ ((1223 / 32 : ℚ) : ℝ) ≤ ((701500985237365 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((350750492618681 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((1223 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-805 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1223 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-805 / 96 : ℚ) : ℝ) ≤ ((701500985237365 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2446 : ((3442192433 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((1223 / 32 : ℚ) : ℝ) ∧
    logKernel ((1223 / 32 : ℚ) : ℝ) ≤ ((13768769737 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2446
  constructor
  · exact (show ((3442192433 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((350750492618681 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1223 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((701500985237365 / 18446744073709551616 : ℚ) : ℝ) ≤ ((13768769737 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2447 : ((345312610260983 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2447 / 64 : ℚ) : ℝ) ∧
    heightZ ((2447 / 64 : ℚ) : ℝ) ≤ ((690625220521969 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((345312610260983 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2447 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1613 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2447 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1613 / 192 : ℚ) : ℝ) ≤ ((690625220521969 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2447 : ((6672574611 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2447 / 64 : ℚ) : ℝ) ∧
    logKernel ((2447 / 64 : ℚ) : ℝ) ≤ ((13345149227 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2447
  constructor
  · exact (show ((6672574611 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((345312610260983 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2447 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((690625220521969 / 18446744073709551616 : ℚ) : ℝ) ≤ ((13345149227 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2448 : ((339959034454975 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((153 / 4 : ℚ) : ℝ) ∧
    heightZ ((153 / 4 : ℚ) : ℝ) ≤ ((679918068909953 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((339959034454975 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((153 / 4 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-101 / 12 : ℚ) : ℝ) ∧
      Real.exp (-((153 / 4 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-101 / 12 : ℚ) : ℝ) ≤ ((679918068909953 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2448 : ((12934562145 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((153 / 4 : ℚ) : ℝ) ∧
    logKernel ((153 / 4 : ℚ) : ℝ) ≤ ((6467281075 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2448
  constructor
  · exact (show ((12934562145 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((339959034454975 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((153 / 4 : ℚ) : ℝ)) hh).trans
      (show zKernel ((679918068909953 / 18446744073709551616 : ℚ) : ℝ) ≤ ((6467281075 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2449 : ((167344229074361 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((2449 / 64 : ℚ) : ℝ) ∧
    heightZ ((2449 / 64 : ℚ) : ℝ) ≤ ((669376916297447 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((167344229074361 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((2449 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1619 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2449 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1619 / 192 : ℚ) : ℝ) ≤ ((669376916297447 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2449 : ((783537969 / 4503599627370496 : ℚ) : ℝ) ≤ logKernel ((2449 / 64 : ℚ) : ℝ) ∧
    logKernel ((2449 / 64 : ℚ) : ℝ) ≤ ((12536607509 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2449
  constructor
  · exact (show ((783537969 / 4503599627370496 : ℚ) : ℝ) ≤ zKernel ((167344229074361 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2449 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((669376916297447 / 18446744073709551616 : ℚ) : ℝ) ≤ ((12536607509 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem log_height_bounds_576 : ((130849851507674195 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((1209 / 32 : ℚ) : ℝ) ∧
    Real.log ((1209 / 32 : ℚ) : ℝ) ≤ ((261699703015348393 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((130849851507674195 / 36028797018963968 : ℚ) : ℝ) ≤ ((1209 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1209 / 32 : ℚ) : ℝ) ≤ Real.exp ((261699703015348393 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_576 : heightPower (576 : Fin 988) ≤ ((1304979627706125 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_576
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_576 : heightFactor (576 : Fin 988) ≤ ((257171013981 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_576
  obtain ⟨hpl, hph⟩ := kernel_bounds_2417
  obtain ⟨hcl, hch⟩ := kernel_bounds_2418
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2418
  have h : (((1461681 / 512 : ℚ) : ℝ) * (logKernel ((2417 / 64 : ℚ) : ℝ) - logKernel ((1209 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1209 / 32 : ℚ) : ℝ) + Real.log ((1209 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((257171013981 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_577 : ((32716187168579937 / 9007199254740992 : ℚ) : ℝ) ≤ Real.log ((2419 / 64 : ℚ) : ℝ) ∧
    Real.log ((2419 / 64 : ℚ) : ℝ) ≤ ((261729497348639499 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((32716187168579937 / 9007199254740992 : ℚ) : ℝ) ≤ ((2419 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2419 / 64 : ℚ) : ℝ) ≤ Real.exp ((261729497348639499 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_577 : heightPower (577 : Fin 988) ≤ ((2614473686037773 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_577
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_577 : heightFactor (577 : Fin 988) ≤ ((250802157903 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_577
  obtain ⟨hpl, hph⟩ := kernel_bounds_2418
  obtain ⟨hcl, hch⟩ := kernel_bounds_2419
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2419
  have h : (((5851561 / 2048 : ℚ) : ℝ) * (logKernel ((1209 / 32 : ℚ) : ℝ) - logKernel ((2419 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2419 / 64 : ℚ) : ℝ) + Real.log ((2419 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((250802157903 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_578 : ((65439819841919503 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((605 / 16 : ℚ) : ℝ) ∧
    Real.log ((605 / 16 : ℚ) : ℝ) ≤ ((261759279367678015 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((65439819841919503 / 18014398509481984 : ℚ) : ℝ) ≤ ((605 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((605 / 16 : ℚ) : ℝ) ≤ Real.exp ((261759279367678015 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_578 : heightPower (578 : Fin 988) ≤ ((1309494034280373 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_578
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_578 : heightFactor (578 : Fin 988) ≤ ((244590929449 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_578
  obtain ⟨hpl, hph⟩ := kernel_bounds_2419
  obtain ⟨hcl, hch⟩ := kernel_bounds_2420
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2420
  have h : (((366025 / 128 : ℚ) : ℝ) * (logKernel ((2419 / 64 : ℚ) : ℝ) - logKernel ((605 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((605 / 16 : ℚ) : ℝ) + Real.log ((605 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((244590929449 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_579 : ((261789049082638907 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2421 / 64 : ℚ) : ℝ) ∧
    Real.log ((2421 / 64 : ℚ) : ℝ) ≤ ((130894524541319455 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((261789049082638907 / 72057594037927936 : ℚ) : ℝ) ≤ ((2421 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2421 / 64 : ℚ) : ℝ) ≤ Real.exp ((130894524541319455 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_579 : heightPower (579 : Fin 988) ≤ ((655875600755229 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_579
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_579 : heightFactor (579 : Fin 988) ≤ ((119266714935 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_579
  obtain ⟨hpl, hph⟩ := kernel_bounds_2420
  obtain ⟨hcl, hch⟩ := kernel_bounds_2421
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2421
  have h : (((5861241 / 2048 : ℚ) : ℝ) * (logKernel ((605 / 16 : ℚ) : ℝ) - logKernel ((2421 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2421 / 64 : ℚ) : ℝ) + Real.log ((2421 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((119266714935 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_580 : ((130909403251842269 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((1211 / 32 : ℚ) : ℝ) ∧
    Real.log ((1211 / 32 : ℚ) : ℝ) ≤ ((261818806503684541 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((130909403251842269 / 36028797018963968 : ℚ) : ℝ) ≤ ((1211 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1211 / 32 : ℚ) : ℝ) ≤ Real.exp ((261818806503684541 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_580 : heightPower (580 : Fin 988) ≤ ((2628016689457979 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_580
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_580 : heightFactor (580 : Fin 988) ≤ ((116312928391 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_580
  obtain ⟨hpl, hph⟩ := kernel_bounds_2421
  obtain ⟨hcl, hch⟩ := kernel_bounds_2422
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2422
  have h : (((1466521 / 512 : ℚ) : ℝ) * (logKernel ((2421 / 64 : ℚ) : ℝ) - logKernel ((1211 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1211 / 32 : ℚ) : ℝ) + Real.log ((1211 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((116312928391 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_581 : ((65462137910241171 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((2423 / 64 : ℚ) : ℝ) ∧
    Real.log ((2423 / 64 : ℚ) : ℝ) ≤ ((261848551640964687 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((65462137910241171 / 18014398509481984 : ℚ) : ℝ) ≤ ((2423 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2423 / 64 : ℚ) : ℝ) ≤ Real.exp ((261848551640964687 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_581 : heightPower (581 : Fin 988) ≤ ((82266591497237 / 8796093022208 : ℚ) : ℝ) := by
  have hh := log_height_bounds_581
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_581 : heightFactor (581 : Fin 988) ≤ ((7089515681 / 8796093022208 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_581
  obtain ⟨hpl, hph⟩ := kernel_bounds_2422
  obtain ⟨hcl, hch⟩ := kernel_bounds_2423
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2423
  have h : (((5870929 / 2048 : ℚ) : ℝ) * (logKernel ((1211 / 32 : ℚ) : ℝ) - logKernel ((2423 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2423 / 64 : ℚ) : ℝ) + Real.log ((2423 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((7089515681 / 8796093022208 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_582 : ((261878284504616555 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((303 / 8 : ℚ) : ℝ) ∧
    Real.log ((303 / 8 : ℚ) : ℝ) ≤ ((130939142252308279 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((261878284504616555 / 72057594037927936 : ℚ) : ℝ) ≤ ((303 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((303 / 8 : ℚ) : ℝ) ≤ Real.exp ((130939142252308279 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_582 : heightPower (582 : Fin 988) ≤ ((164815319901333 / 17592186044416 : ℚ) : ℝ) := by
  have hh := log_height_bounds_582
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_582 : heightFactor (582 : Fin 988) ≤ ((221245748171 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_582
  obtain ⟨hpl, hph⟩ := kernel_bounds_2423
  obtain ⟨hcl, hch⟩ := kernel_bounds_2424
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2424
  have h : (((91809 / 32 : ℚ) : ℝ) * (logKernel ((2423 / 64 : ℚ) : ℝ) - logKernel ((303 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((303 / 8 : ℚ) : ℝ) + Real.log ((303 / 8 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((221245748171 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_583 : ((130954002552382409 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2425 / 64 : ℚ) : ℝ) ∧
    Real.log ((2425 / 64 : ℚ) : ℝ) ≤ ((261908005104764821 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((130954002552382409 / 36028797018963968 : ℚ) : ℝ) ≤ ((2425 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2425 / 64 : ℚ) : ℝ) ≤ Real.exp ((261908005104764821 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_583 : heightPower (583 : Fin 988) ≤ ((2641559261026761 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_583
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_583 : heightFactor (583 : Fin 988) ≤ ((107883034295 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_583
  obtain ⟨hpl, hph⟩ := kernel_bounds_2424
  obtain ⟨hcl, hch⟩ := kernel_bounds_2425
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2425
  have h : (((5880625 / 2048 : ℚ) : ℝ) * (logKernel ((303 / 8 : ℚ) : ℝ) - logKernel ((2425 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2425 / 64 : ℚ) : ℝ) + Real.log ((2425 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((107883034295 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_584 : ((65484428362880405 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((1213 / 32 : ℚ) : ℝ) ∧
    Real.log ((1213 / 32 : ℚ) : ℝ) ≤ ((261937713451521623 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((65484428362880405 / 18014398509481984 : ℚ) : ℝ) ≤ ((1213 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1213 / 32 : ℚ) : ℝ) ≤ Real.exp ((261937713451521623 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_584 : heightPower (584 : Fin 988) ≤ ((330759169470923 / 35184372088832 : ℚ) : ℝ) := by
  have hh := log_height_bounds_584
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_584 : heightFactor (584 : Fin 988) ≤ ((210422022915 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_584
  obtain ⟨hpl, hph⟩ := kernel_bounds_2425
  obtain ⟨hcl, hch⟩ := kernel_bounds_2426
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2426
  have h : (((1471369 / 512 : ℚ) : ℝ) * (logKernel ((2425 / 64 : ℚ) : ℝ) - logKernel ((1213 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1213 / 32 : ℚ) : ℝ) + Real.log ((1213 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((210422022915 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_585 : ((261967409554986603 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2427 / 64 : ℚ) : ℝ) ∧
    Real.log ((2427 / 64 : ℚ) : ℝ) ≤ ((130983704777493303 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((261967409554986603 / 72057594037927936 : ℚ) : ℝ) ≤ ((2427 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2427 / 64 : ℚ) : ℝ) ≤ Real.exp ((130983704777493303 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_585 : heightPower (585 : Fin 988) ≤ ((331323425335331 / 35184372088832 : ℚ) : ℝ) := by
  have hh := log_height_bounds_585
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_585 : heightFactor (585 : Fin 988) ≤ ((102605128025 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_585
  obtain ⟨hpl, hph⟩ := kernel_bounds_2426
  obtain ⟨hcl, hch⟩ := kernel_bounds_2427
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2427
  have h : (((5890329 / 2048 : ℚ) : ℝ) * (logKernel ((1213 / 32 : ℚ) : ℝ) - logKernel ((2427 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2427 / 64 : ℚ) : ℝ) + Real.log ((2427 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((102605128025 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_586 : ((261997093425246929 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((607 / 16 : ℚ) : ℝ) ∧
    Real.log ((607 / 16 : ℚ) : ℝ) ≤ ((65499273356311733 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((261997093425246929 / 72057594037927936 : ℚ) : ℝ) ≤ ((607 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((607 / 16 : ℚ) : ℝ) ≤ Real.exp ((65499273356311733 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_586 : heightPower (586 : Fin 988) ≤ ((663775350452989 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_586
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_586 : heightFactor (586 : Fin 988) ≤ ((200127495837 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_586
  obtain ⟨hpl, hph⟩ := kernel_bounds_2427
  obtain ⟨hcl, hch⟩ := kernel_bounds_2428
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2428
  have h : (((368449 / 128 : ℚ) : ℝ) * (logKernel ((2427 / 64 : ℚ) : ℝ) - logKernel ((607 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((607 / 16 : ℚ) : ℝ) + Real.log ((607 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((200127495837 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_587 : ((262026765072377299 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2429 / 64 : ℚ) : ℝ) ∧
    Real.log ((2429 / 64 : ℚ) : ℝ) ≤ ((131013382536188651 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((262026765072377299 / 72057594037927936 : ℚ) : ℝ) ≤ ((2429 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2429 / 64 : ℚ) : ℝ) ≤ Real.exp ((131013382536188651 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_587 : heightPower (587 : Fin 988) ≤ ((2659615353194663 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_587
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_587 : heightFactor (587 : Fin 988) ≤ ((195170551009 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_587
  obtain ⟨hpl, hph⟩ := kernel_bounds_2428
  obtain ⟨hcl, hch⟩ := kernel_bounds_2429
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2429
  have h : (((5900041 / 2048 : ℚ) : ℝ) * (logKernel ((607 / 16 : ℚ) : ℝ) - logKernel ((2429 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2429 / 64 : ℚ) : ℝ) + Real.log ((2429 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((195170551009 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_588 : ((65514106126609993 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((1215 / 32 : ℚ) : ℝ) ∧
    Real.log ((1215 / 32 : ℚ) : ℝ) ≤ ((262056424506439975 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((65514106126609993 / 18014398509481984 : ℚ) : ℝ) ≤ ((1215 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1215 / 32 : ℚ) : ℝ) ≤ Real.exp ((262056424506439975 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_588 : heightPower (588 : Fin 988) ≤ ((2664129256870075 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_588
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_588 : heightFactor (588 : Fin 988) ≤ ((95168154595 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_588
  obtain ⟨hpl, hph⟩ := kernel_bounds_2429
  obtain ⟨hcl, hch⟩ := kernel_bounds_2430
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2430
  have h : (((1476225 / 512 : ℚ) : ℝ) * (logKernel ((2429 / 64 : ℚ) : ℝ) - logKernel ((1215 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1215 / 32 : ℚ) : ℝ) + Real.log ((1215 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((95168154595 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_589 : ((262086071737484789 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2431 / 64 : ℚ) : ℝ) ∧
    Real.log ((2431 / 64 : ℚ) : ℝ) ≤ ((32760758967185599 / 9007199254740992 : ℚ) : ℝ) := by
  have hl : Real.exp ((262086071737484789 / 72057594037927936 : ℚ) : ℝ) ≤ ((2431 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2431 / 64 : ℚ) : ℝ) ≤ Real.exp ((32760758967185599 / 9007199254740992 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_589 : heightPower (589 : Fin 988) ≤ ((2668643112877447 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_589
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_589 : heightFactor (589 : Fin 988) ≤ ((5800679217 / 8796093022208 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_589
  obtain ⟨hpl, hph⟩ := kernel_bounds_2430
  obtain ⟨hcl, hch⟩ := kernel_bounds_2431
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2431
  have h : (((5909761 / 2048 : ℚ) : ℝ) * (logKernel ((1215 / 32 : ℚ) : ℝ) - logKernel ((2431 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2431 / 64 : ℚ) : ℝ) + Real.log ((2431 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((5800679217 / 8796093022208 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_590 : ((131057853387774595 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((38 / 1 : ℚ) : ℝ) ∧
    Real.log ((38 / 1 : ℚ) : ℝ) ≤ ((262115706775549193 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((131057853387774595 / 36028797018963968 : ℚ) : ℝ) ≤ ((38 / 1 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((38 / 1 : ℚ) : ℝ) ≤ Real.exp ((262115706775549193 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_590 : heightPower (590 : Fin 988) ≤ ((2673156921255991 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_590
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_590 : heightFactor (590 : Fin 988) ≤ ((181023867879 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_590
  obtain ⟨hpl, hph⟩ := kernel_bounds_2431
  obtain ⟨hcl, hch⟩ := kernel_bounds_2432
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2432
  have h : (((2888 / 1 : ℚ) : ℝ) * (logKernel ((2431 / 64 : ℚ) : ℝ) - logKernel ((38 / 1 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((38 / 1 : ℚ) : ℝ) + Real.log ((38 / 1 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((181023867879 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_591 : ((262145329630658237 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2433 / 64 : ℚ) : ℝ) ∧
    Real.log ((2433 / 64 : ℚ) : ℝ) ≤ ((4096020775479035 / 1125899906842624 : ℚ) : ℝ) := by
  have hl : Real.exp ((262145329630658237 / 72057594037927936 : ℚ) : ℝ) ≤ ((2433 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2433 / 64 : ℚ) : ℝ) ≤ Real.exp ((4096020775479035 / 1125899906842624 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_591 : heightPower (591 : Fin 988) ≤ ((41838604406951 / 4398046511104 : ℚ) : ℝ) := by
  have hh := log_height_bounds_591
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_591 : heightFactor (591 : Fin 988) ≤ ((176539820789 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_591
  obtain ⟨hpl, hph⟩ := kernel_bounds_2432
  obtain ⟨hcl, hch⟩ := kernel_bounds_2433
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2433
  have h : (((5919489 / 2048 : ℚ) : ℝ) * (logKernel ((38 / 1 : ℚ) : ℝ) - logKernel ((2433 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2433 / 64 : ℚ) : ℝ) + Real.log ((2433 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((176539820789 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_592 : ((262174940312824633 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1217 / 32 : ℚ) : ℝ) ∧
    Real.log ((1217 / 32 : ℚ) : ℝ) ≤ ((65543735078206159 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((262174940312824633 / 72057594037927936 : ℚ) : ℝ) ≤ ((1217 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1217 / 32 : ℚ) : ℝ) ≤ Real.exp ((65543735078206159 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_592 : heightPower (592 : Fin 988) ≤ ((2682184395283181 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_592
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_592 : heightFactor (592 : Fin 988) ≤ ((172166777849 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_592
  obtain ⟨hpl, hph⟩ := kernel_bounds_2433
  obtain ⟨hcl, hch⟩ := kernel_bounds_2434
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2434
  have h : (((1481089 / 512 : ℚ) : ℝ) * (logKernel ((2433 / 64 : ℚ) : ℝ) - logKernel ((1217 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1217 / 32 : ℚ) : ℝ) + Real.log ((1217 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((172166777849 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_593 : ((65551134708012185 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((2435 / 64 : ℚ) : ℝ) ∧
    Real.log ((2435 / 64 : ℚ) : ℝ) ≤ ((262204538832048743 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((65551134708012185 / 18014398509481984 : ℚ) : ℝ) ≤ ((2435 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2435 / 64 : ℚ) : ℝ) ≤ Real.exp ((262204538832048743 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_593 : heightPower (593 : Fin 988) ≤ ((671674515252501 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_593
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_593 : heightFactor (593 : Fin 988) ≤ ((10493874553 / 17592186044416 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_593
  obtain ⟨hpl, hph⟩ := kernel_bounds_2434
  obtain ⟨hcl, hch⟩ := kernel_bounds_2435
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2435
  have h : (((5929225 / 2048 : ℚ) : ℝ) * (logKernel ((1217 / 32 : ℚ) : ℝ) - logKernel ((2435 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2435 / 64 : ℚ) : ℝ) + Real.log ((2435 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((10493874553 / 17592186044416 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_594 : ((131117062599159303 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((609 / 16 : ℚ) : ℝ) ∧
    Real.log ((609 / 16 : ℚ) : ℝ) ≤ ((262234125198318609 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((131117062599159303 / 36028797018963968 : ℚ) : ℝ) ≤ ((609 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((609 / 16 : ℚ) : ℝ) ≤ Real.exp ((262234125198318609 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_594 : heightPower (594 : Fin 988) ≤ ((1345605839632175 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_594
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_594 : heightFactor (594 : Fin 988) ≤ ((163742787473 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_594
  obtain ⟨hpl, hph⟩ := kernel_bounds_2435
  obtain ⟨hcl, hch⟩ := kernel_bounds_2436
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2436
  have h : (((370881 / 128 : ℚ) : ℝ) * (logKernel ((2435 / 64 : ℚ) : ℝ) - logKernel ((609 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((609 / 16 : ℚ) : ℝ) + Real.log ((609 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((163742787473 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_595 : ((131131849710804989 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2437 / 64 : ℚ) : ℝ) ∧
    Real.log ((2437 / 64 : ℚ) : ℝ) ≤ ((262263699421609981 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((131131849710804989 / 36028797018963968 : ℚ) : ℝ) ≤ ((2437 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2437 / 64 : ℚ) : ℝ) ≤ Real.exp ((262263699421609981 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_595 : heightPower (595 : Fin 988) ≤ ((2695725250085185 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_595
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_595 : heightFactor (595 : Fin 988) ≤ ((159686549629 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_595
  obtain ⟨hpl, hph⟩ := kernel_bounds_2436
  obtain ⟨hcl, hch⟩ := kernel_bounds_2437
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2437
  have h : (((5938969 / 2048 : ℚ) : ℝ) * (logKernel ((609 / 16 : ℚ) : ℝ) - logKernel ((2437 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2437 / 64 : ℚ) : ℝ) + Real.log ((2437 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((159686549629 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_596 : ((131146630755943163 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((1219 / 32 : ℚ) : ℝ) ∧
    Real.log ((1219 / 32 : ℚ) : ℝ) ≤ ((262293261511886329 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((131146630755943163 / 36028797018963968 : ℚ) : ℝ) ≤ ((1219 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1219 / 32 : ℚ) : ℝ) ≤ Real.exp ((262293261511886329 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_596 : heightPower (596 : Fin 988) ≤ ((2700238773511431 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_596
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_596 : heightFactor (596 : Fin 988) ≤ ((77865365901 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_596
  obtain ⟨hpl, hph⟩ := kernel_bounds_2437
  obtain ⟨hcl, hch⟩ := kernel_bounds_2438
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2438
  have h : (((1485961 / 512 : ℚ) : ℝ) * (logKernel ((2437 / 64 : ℚ) : ℝ) - logKernel ((1219 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1219 / 32 : ℚ) : ℝ) + Real.log ((1219 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((77865365901 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_597 : ((131161405739549431 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2439 / 64 : ℚ) : ℝ) ∧
    Real.log ((2439 / 64 : ℚ) : ℝ) ≤ ((262322811479098865 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((131161405739549431 / 36028797018963968 : ℚ) : ℝ) ≤ ((2439 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2439 / 64 : ℚ) : ℝ) ≤ Real.exp ((262322811479098865 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_597 : heightPower (597 : Fin 988) ≤ ((2704752249581959 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_597
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_597 : heightFactor (597 : Fin 988) ≤ ((75936424733 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_597
  obtain ⟨hpl, hph⟩ := kernel_bounds_2438
  obtain ⟨hcl, hch⟩ := kernel_bounds_2439
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2439
  have h : (((5948721 / 2048 : ℚ) : ℝ) * (logKernel ((1219 / 32 : ℚ) : ℝ) - logKernel ((2439 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2439 / 64 : ℚ) : ℝ) + Real.log ((2439 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((75936424733 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_598 : ((262352349333186561 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((305 / 8 : ℚ) : ℝ) ∧
    Real.log ((305 / 8 : ℚ) : ℝ) ≤ ((65588087333296641 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((262352349333186561 / 72057594037927936 : ℚ) : ℝ) ≤ ((305 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((305 / 8 : ℚ) : ℝ) ≤ Real.exp ((65588087333296641 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_598 : heightPower (598 : Fin 988) ≤ ((1354632839167797 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_598
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_598 : heightFactor (598 : Fin 988) ≤ ((148110479525 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_598
  obtain ⟨hpl, hph⟩ := kernel_bounds_2439
  obtain ⟨hcl, hch⟩ := kernel_bounds_2440
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2440
  have h : (((93025 / 32 : ℚ) : ℝ) * (logKernel ((2439 / 64 : ℚ) : ℝ) - logKernel ((305 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((305 / 8 : ℚ) : ℝ) + Real.log ((305 / 8 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((148110479525 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_599 : ((262381875084076179 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2441 / 64 : ℚ) : ℝ) ∧
    Real.log ((2441 / 64 : ℚ) : ℝ) ≤ ((131190937542038091 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((262381875084076179 / 72057594037927936 : ℚ) : ℝ) ≤ ((2441 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2441 / 64 : ℚ) : ℝ) ≤ Real.exp ((131190937542038091 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_599 : heightPower (599 : Fin 988) ≤ ((1356889529905555 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_599
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_599 : heightFactor (599 : Fin 988) ≤ ((36110314699 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_599
  obtain ⟨hpl, hph⟩ := kernel_bounds_2440
  obtain ⟨hcl, hch⟩ := kernel_bounds_2441
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2441
  have h : (((5958481 / 2048 : ℚ) : ℝ) * (logKernel ((305 / 8 : ℚ) : ℝ) - logKernel ((2441 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2441 / 64 : ℚ) : ℝ) + Real.log ((2441 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((36110314699 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_600 : ((131205694370841139 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((1221 / 32 : ℚ) : ℝ) ∧
    Real.log ((1221 / 32 : ℚ) : ℝ) ≤ ((262411388741682281 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((131205694370841139 / 36028797018963968 : ℚ) : ℝ) ≤ ((1221 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1221 / 32 : ℚ) : ℝ) ≤ Real.exp ((262411388741682281 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_600 : heightPower (600 : Fin 988) ≤ ((1359146197023619 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_600
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_600 : heightFactor (600 : Fin 988) ≤ ((4401965079 / 8796093022208 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_600
  obtain ⟨hpl, hph⟩ := kernel_bounds_2441
  obtain ⟨hcl, hch⟩ := kernel_bounds_2442
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2442
  have h : (((1490841 / 512 : ℚ) : ℝ) * (logKernel ((2441 / 64 : ℚ) : ℝ) - logKernel ((1221 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1221 / 32 : ℚ) : ℝ) + Real.log ((1221 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((4401965079 / 8796093022208 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_601 : ((262440890315907237 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2443 / 64 : ℚ) : ℝ) ∧
    Real.log ((2443 / 64 : ℚ) : ℝ) ≤ ((32805111289488405 / 9007199254740992 : ℚ) : ℝ) := by
  have hl : Real.exp ((262440890315907237 / 72057594037927936 : ℚ) : ℝ) ≤ ((2443 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2443 / 64 : ℚ) : ℝ) ≤ Real.exp ((32805111289488405 / 9007199254740992 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_601 : heightPower (601 : Fin 988) ≤ ((1361402840541329 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_601
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_601 : heightFactor (601 : Fin 988) ≤ ((68686551479 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_601
  obtain ⟨hpl, hph⟩ := kernel_bounds_2442
  obtain ⟨hcl, hch⟩ := kernel_bounds_2443
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2443
  have h : (((5968249 / 2048 : ℚ) : ℝ) * (logKernel ((1221 / 32 : ℚ) : ℝ) - logKernel ((2443 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2443 / 64 : ℚ) : ℝ) + Real.log ((2443 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((68686551479 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_602 : ((262470379816641283 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((611 / 16 : ℚ) : ℝ) ∧
    Real.log ((611 / 16 : ℚ) : ℝ) ≤ ((131235189908320643 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((262470379816641283 / 72057594037927936 : ℚ) : ℝ) ≤ ((611 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((611 / 16 : ℚ) : ℝ) ≤ Real.exp ((131235189908320643 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_602 : heightPower (602 : Fin 988) ≤ ((2727318920956005 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_602
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_602 : heightFactor (602 : Fin 988) ≤ ((133969727905 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_602
  obtain ⟨hpl, hph⟩ := kernel_bounds_2443
  obtain ⟨hcl, hch⟩ := kernel_bounds_2444
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2444
  have h : (((373321 / 128 : ℚ) : ℝ) * (logKernel ((2443 / 64 : ℚ) : ℝ) - logKernel ((611 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((611 / 16 : ℚ) : ℝ) + Real.log ((611 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((133969727905 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_603 : ((262499857253762501 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2445 / 64 : ℚ) : ℝ) ∧
    Real.log ((2445 / 64 : ℚ) : ℝ) ≤ ((32812482156720313 / 9007199254740992 : ℚ) : ℝ) := by
  have hl : Real.exp ((262499857253762501 / 72057594037927936 : ℚ) : ℝ) ≤ ((2445 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2445 / 64 : ℚ) : ℝ) ≤ Real.exp ((32812482156720313 / 9007199254740992 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_603 : heightPower (603 : Fin 988) ≤ ((2731832113705863 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_603
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_603 : heightFactor (603 : Fin 988) ≤ ((255176991 / 549755813888 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_603
  obtain ⟨hpl, hph⟩ := kernel_bounds_2444
  obtain ⟨hcl, hch⟩ := kernel_bounds_2445
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2445
  have h : (((5978025 / 2048 : ℚ) : ℝ) * (logKernel ((611 / 16 : ℚ) : ℝ) - logKernel ((2445 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2445 / 64 : ℚ) : ℝ) + Real.log ((2445 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((255176991 / 549755813888 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_604 : ((65632330659284215 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((1223 / 32 : ℚ) : ℝ) ∧
    Real.log ((1223 / 32 : ℚ) : ℝ) ≤ ((262529322637136863 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((65632330659284215 / 18014398509481984 : ℚ) : ℝ) ≤ ((1223 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1223 / 32 : ℚ) : ℝ) ≤ Real.exp ((262529322637136863 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_604 : heightPower (604 : Fin 988) ≤ ((2736345259370773 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_604
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_604 : heightFactor (604 : Fin 988) ≤ ((15926711539 / 35184372088832 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_604
  obtain ⟨hpl, hph⟩ := kernel_bounds_2445
  obtain ⟨hcl, hch⟩ := kernel_bounds_2446
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2446
  have h : (((1495729 / 512 : ℚ) : ℝ) * (logKernel ((2445 / 64 : ℚ) : ℝ) - logKernel ((1223 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1223 / 32 : ℚ) : ℝ) + Real.log ((1223 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((15926711539 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_605 : ((32819846997077279 / 9007199254740992 : ℚ) : ℝ) ≤ Real.log ((2447 / 64 : ℚ) : ℝ) ∧
    Real.log ((2447 / 64 : ℚ) : ℝ) ≤ ((262558775976618235 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((32819846997077279 / 9007199254740992 : ℚ) : ℝ) ≤ ((2447 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2447 / 64 : ℚ) : ℝ) ≤ Real.exp ((262558775976618235 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_605 : heightPower (605 : Fin 988) ≤ ((1370429178994613 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_605
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_605 : heightFactor (605 : Fin 988) ≤ ((124256913117 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_605
  obtain ⟨hpl, hph⟩ := kernel_bounds_2446
  obtain ⟨hcl, hch⟩ := kernel_bounds_2447
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2447
  have h : (((5987809 / 2048 : ℚ) : ℝ) * (logKernel ((1223 / 32 : ℚ) : ℝ) - logKernel ((2447 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2447 / 64 : ℚ) : ℝ) + Real.log ((2447 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((124256913117 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_606 : ((32823527160256051 / 9007199254740992 : ℚ) : ℝ) ≤ Real.log ((153 / 4 : ℚ) : ℝ) ∧
    Real.log ((153 / 4 : ℚ) : ℝ) ≤ ((262588217282048411 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((32823527160256051 / 9007199254740992 : ℚ) : ℝ) ≤ ((153 / 4 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((153 / 4 : ℚ) : ℝ) ≤ Real.exp ((262588217282048411 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_606 : heightPower (606 : Fin 988) ≤ ((2745371409599667 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_606
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_606 : heightFactor (606 : Fin 988) ≤ ((121178298547 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_606
  obtain ⟨hpl, hph⟩ := kernel_bounds_2447
  obtain ⟨hcl, hch⟩ := kernel_bounds_2448
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2448
  have h : (((23409 / 8 : ℚ) : ℝ) * (logKernel ((2447 / 64 : ℚ) : ℝ) - logKernel ((153 / 4 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((153 / 4 : ℚ) : ℝ) + Real.log ((153 / 4 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((121178298547 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_607 : ((131308823281628561 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2449 / 64 : ℚ) : ℝ) ∧
    Real.log ((2449 / 64 : ℚ) : ℝ) ≤ ((262617646563257125 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((131308823281628561 / 36028797018963968 : ℚ) : ℝ) ≤ ((2449 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2449 / 64 : ℚ) : ℝ) ≤ Real.exp ((262617646563257125 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_607 : heightPower (607 : Fin 988) ≤ ((2749884414240493 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_607
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_607 : heightFactor (607 : Fin 988) ≤ ((7385994649 / 17592186044416 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_607
  obtain ⟨hpl, hph⟩ := kernel_bounds_2448
  obtain ⟨hcl, hch⟩ := kernel_bounds_2449
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2449
  have h : (((5997601 / 2048 : ℚ) : ℝ) * (logKernel ((153 / 4 : ℚ) : ℝ) - logKernel ((2449 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2449 / 64 : ℚ) : ℝ) + Real.log ((2449 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((7385994649 / 17592186044416 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

end LegendreK6.M2Pilot.Enclosures.Height018
