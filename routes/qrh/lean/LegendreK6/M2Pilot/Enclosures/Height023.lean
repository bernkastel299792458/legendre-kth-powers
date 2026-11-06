import LegendreK6.M2PilotDefinitions
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp

/-! Generated proposals: every bound is checked by Lean, not by trusting Arb. -/
namespace LegendreK6.M2Pilot.Enclosures.Height023
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem height_z_bounds_2577 : ((22647578639791 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((2577 / 64 : ℚ) : ℝ) ∧
    heightZ ((2577 / 64 : ℚ) : ℝ) ≤ ((90590314559167 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((22647578639791 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((2577 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2003 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2577 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2003 / 192 : ℚ) : ℝ) ≤ ((90590314559167 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2577 : ((229615973 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2577 / 64 : ℚ) : ℝ) ∧
    logKernel ((2577 / 64 : ℚ) : ℝ) ≤ ((114807989 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2577
  constructor
  · exact (show ((229615973 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((22647578639791 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2577 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((90590314559167 / 18446744073709551616 : ℚ) : ℝ) ≤ ((114807989 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2578 : ((11148230238837 / 2305843009213693952 : ℚ) : ℝ) ≤ heightZ ((1289 / 32 : ℚ) : ℝ) ∧
    heightZ ((1289 / 32 : ℚ) : ℝ) ≤ ((89185841910699 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((11148230238837 / 2305843009213693952 : ℚ) : ℝ) ≤ Real.exp (-((1289 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1003 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1289 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1003 / 96 : ℚ) : ℝ) ≤ ((89185841910699 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2578 : ((222551433 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1289 / 32 : ℚ) : ℝ) ∧
    logKernel ((1289 / 32 : ℚ) : ℝ) ≤ ((111275719 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2578
  constructor
  · exact (show ((222551433 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((11148230238837 / 2305843009213693952 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1289 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((89185841910699 / 18446744073709551616 : ℚ) : ℝ) ≤ ((111275719 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2579 : ((10975392949051 / 2305843009213693952 : ℚ) : ℝ) ≤ heightZ ((2579 / 64 : ℚ) : ℝ) ∧
    heightZ ((2579 / 64 : ℚ) : ℝ) ≤ ((87803143592411 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((10975392949051 / 2305843009213693952 : ℚ) : ℝ) ≤ Real.exp (-((2579 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2009 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2579 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2009 / 192 : ℚ) : ℝ) ≤ ((87803143592411 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2579 : ((215704245 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2579 / 64 : ℚ) : ℝ) ∧
    logKernel ((2579 / 64 : ℚ) : ℝ) ≤ ((107852125 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2579
  constructor
  · exact (show ((215704245 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((10975392949051 / 2305843009213693952 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2579 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((87803143592411 / 18446744073709551616 : ℚ) : ℝ) ≤ ((107852125 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2580 : ((86441882024599 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((645 / 16 : ℚ) : ℝ) ∧
    heightZ ((645 / 16 : ℚ) : ℝ) ≤ ((43220941012301 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((86441882024599 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((645 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-503 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((645 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-503 / 48 : ℚ) : ℝ) ≤ ((43220941012301 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2580 : ((209067723 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((645 / 16 : ℚ) : ℝ) ∧
    logKernel ((645 / 16 : ℚ) : ℝ) ≤ ((13066733 / 4503599627370496 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2580
  constructor
  · exact (show ((209067723 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((86441882024599 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((645 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((43220941012301 / 9223372036854775808 : ℚ) : ℝ) ≤ ((13066733 / 4503599627370496 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2581 : ((21275431215315 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((2581 / 64 : ℚ) : ℝ) ∧
    heightZ ((2581 / 64 : ℚ) : ℝ) ≤ ((85101724861263 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((21275431215315 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((2581 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2015 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2581 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2015 / 192 : ℚ) : ℝ) ≤ ((85101724861263 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2581 : ((202635385 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2581 / 64 : ℚ) : ℝ) ∧
    logKernel ((2581 / 64 : ℚ) : ℝ) ≤ ((101317695 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2581
  constructor
  · exact (show ((202635385 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((21275431215315 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2581 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((85101724861263 / 18446744073709551616 : ℚ) : ℝ) ≤ ((101317695 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2582 : ((83782344908925 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1291 / 32 : ℚ) : ℝ) ∧
    heightZ ((1291 / 32 : ℚ) : ℝ) ≤ ((654549569601 / 144115188075855872 : ℚ) : ℝ) := by
  have h : ((83782344908925 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1291 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1009 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1291 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1009 / 96 : ℚ) : ℝ) ≤ ((654549569601 / 144115188075855872 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2582 : ((98200475 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((1291 / 32 : ℚ) : ℝ) ∧
    logKernel ((1291 / 32 : ℚ) : ℝ) ≤ ((196400955 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2582
  constructor
  · exact (show ((98200475 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((83782344908925 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1291 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((654549569601 / 144115188075855872 : ℚ) : ℝ) ≤ ((196400955 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2583 : ((82483420046795 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2583 / 64 : ℚ) : ℝ) ∧
    heightZ ((2583 / 64 : ℚ) : ℝ) ≤ ((41241710023399 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((82483420046795 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2583 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2021 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2583 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2021 / 192 : ℚ) : ℝ) ≤ ((41241710023399 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2583 : ((23794791 / 9007199254740992 : ℚ) : ℝ) ≤ logKernel ((2583 / 64 : ℚ) : ℝ) ∧
    logKernel ((2583 / 64 : ℚ) : ℝ) ≤ ((190358333 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2583
  constructor
  · exact (show ((23794791 / 9007199254740992 : ℚ) : ℝ) ≤ zKernel ((82483420046795 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2583 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((41241710023399 / 9223372036854775808 : ℚ) : ℝ) ≤ ((190358333 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2584 : ((40602316574045 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((323 / 8 : ℚ) : ℝ) ∧
    heightZ ((323 / 8 : ℚ) : ℝ) ≤ ((81204633148093 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((40602316574045 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((323 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-253 / 24 : ℚ) : ℝ) ∧
      Real.exp (-((323 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-253 / 24 : ℚ) : ℝ) ≤ ((81204633148093 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2584 : ((184501617 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((323 / 8 : ℚ) : ℝ) ∧
    logKernel ((323 / 8 : ℚ) : ℝ) ≤ ((92250811 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2584
  constructor
  · exact (show ((184501617 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((40602316574045 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((323 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((81204633148093 / 18446744073709551616 : ℚ) : ℝ) ≤ ((92250811 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2585 : ((39972836001313 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2585 / 64 : ℚ) : ℝ) ∧
    heightZ ((2585 / 64 : ℚ) : ℝ) ≤ ((79945672002629 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((39972836001313 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2585 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2027 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2585 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2027 / 192 : ℚ) : ℝ) ≤ ((79945672002629 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2585 : ((178825099 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2585 / 64 : ℚ) : ℝ) ∧
    logKernel ((2585 / 64 : ℚ) : ℝ) ≤ ((11176569 / 4503599627370496 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2585
  constructor
  · exact (show ((178825099 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((39972836001313 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2585 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((79945672002629 / 18446744073709551616 : ℚ) : ℝ) ≤ ((11176569 / 4503599627370496 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2586 : ((19676557310147 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((1293 / 32 : ℚ) : ℝ) ∧
    heightZ ((1293 / 32 : ℚ) : ℝ) ≤ ((78706229240591 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((19676557310147 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((1293 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1015 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1293 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1015 / 96 : ℚ) : ℝ) ≤ ((78706229240591 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2586 : ((173323229 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1293 / 32 : ℚ) : ℝ) ∧
    logKernel ((1293 / 32 : ℚ) : ℝ) ≤ ((86661617 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2586
  constructor
  · exact (show ((173323229 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((19676557310147 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1293 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((78706229240591 / 18446744073709551616 : ℚ) : ℝ) ≤ ((86661617 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2587 : ((38743001128745 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2587 / 64 : ℚ) : ℝ) ∧
    heightZ ((2587 / 64 : ℚ) : ℝ) ≤ ((77486002257493 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((38743001128745 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2587 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2033 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2587 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2033 / 192 : ℚ) : ℝ) ≤ ((77486002257493 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2587 : ((83995317 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2587 / 64 : ℚ) : ℝ) ∧
    logKernel ((2587 / 64 : ℚ) : ℝ) ≤ ((167990639 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2587
  constructor
  · exact (show ((83995317 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((38743001128745 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2587 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((77486002257493 / 18446744073709551616 : ℚ) : ℝ) ≤ ((167990639 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2588 : ((19071173285073 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((647 / 16 : ℚ) : ℝ) ∧
    heightZ ((647 / 16 : ℚ) : ℝ) ≤ ((76284693140295 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((19071173285073 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((647 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-509 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((647 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-509 / 48 : ℚ) : ℝ) ≤ ((76284693140295 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2588 : ((81411053 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((647 / 16 : ℚ) : ℝ) ∧
    logKernel ((647 / 16 : ℚ) : ℝ) ≤ ((162822111 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2588
  constructor
  · exact (show ((81411053 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((19071173285073 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((647 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((76284693140295 / 18446744073709551616 : ℚ) : ℝ) ≤ ((162822111 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2589 : ((18775502148667 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((2589 / 64 : ℚ) : ℝ) ∧
    heightZ ((2589 / 64 : ℚ) : ℝ) ≤ ((75102008594671 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((18775502148667 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((2589 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2039 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2589 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2039 / 192 : ℚ) : ℝ) ≤ ((75102008594671 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2589 : ((39453149 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((2589 / 64 : ℚ) : ℝ) ∧
    logKernel ((2589 / 64 : ℚ) : ℝ) ≤ ((157812601 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2589
  constructor
  · exact (show ((39453149 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((18775502148667 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2589 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((75102008594671 / 18446744073709551616 : ℚ) : ℝ) ≤ ((157812601 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2590 : ((9242207484175 / 2305843009213693952 : ℚ) : ℝ) ≤ heightZ ((1295 / 32 : ℚ) : ℝ) ∧
    heightZ ((1295 / 32 : ℚ) : ℝ) ≤ ((73937659873403 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((9242207484175 / 2305843009213693952 : ℚ) : ℝ) ≤ Real.exp (-((1295 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1021 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1295 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1021 / 96 : ℚ) : ℝ) ≤ ((73937659873403 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2590 : ((152957213 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1295 / 32 : ℚ) : ℝ) ∧
    logKernel ((1295 / 32 : ℚ) : ℝ) ≤ ((76478609 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2590
  constructor
  · exact (show ((152957213 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((9242207484175 / 2305843009213693952 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1295 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((73937659873403 / 18446744073709551616 : ℚ) : ℝ) ≤ ((76478609 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2591 : ((9098920338235 / 2305843009213693952 : ℚ) : ℝ) ≤ heightZ ((2591 / 64 : ℚ) : ℝ) ∧
    heightZ ((2591 / 64 : ℚ) : ℝ) ≤ ((72791362705883 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((9098920338235 / 2305843009213693952 : ℚ) : ℝ) ≤ Real.exp (-((2591 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2045 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2591 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2045 / 192 : ℚ) : ℝ) ≤ ((72791362705883 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2591 : ((74125607 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2591 / 64 : ℚ) : ℝ) ∧
    logKernel ((2591 / 64 : ℚ) : ℝ) ≤ ((148251219 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2591
  constructor
  · exact (show ((74125607 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((9098920338235 / 2305843009213693952 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2591 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((72791362705883 / 18446744073709551616 : ℚ) : ℝ) ≤ ((148251219 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2592 : ((17915709307177 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((81 / 2 : ℚ) : ℝ) ∧
    heightZ ((81 / 2 : ℚ) : ℝ) ≤ ((71662837228711 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((17915709307177 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((81 / 2 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-32 / 3 : ℚ) : ℝ) ∧
      Real.exp (-((81 / 2 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-32 / 3 : ℚ) : ℝ) ≤ ((71662837228711 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2592 : ((35922501 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((81 / 2 : ℚ) : ℝ) ∧
    logKernel ((81 / 2 : ℚ) : ℝ) ≤ ((143690009 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2592
  constructor
  · exact (show ((35922501 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((17915709307177 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((81 / 2 : ℚ) : ℝ)) hh).trans
      (show zKernel ((71662837228711 / 18446744073709551616 : ℚ) : ℝ) ≤ ((143690009 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2593 : ((70551807917361 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2593 / 64 : ℚ) : ℝ) ∧
    heightZ ((2593 / 64 : ℚ) : ℝ) ≤ ((17637951979341 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((70551807917361 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2593 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2051 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2593 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2051 / 192 : ℚ) : ℝ) ≤ ((17637951979341 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2593 : ((139269127 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2593 / 64 : ℚ) : ℝ) ∧
    logKernel ((2593 / 64 : ℚ) : ℝ) ≤ ((34817283 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2593
  constructor
  · exact (show ((139269127 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((70551807917361 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2593 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((17637951979341 / 4611686018427387904 : ℚ) : ℝ) ≤ ((34817283 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2594 : ((17364500879733 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((1297 / 32 : ℚ) : ℝ) ∧
    heightZ ((1297 / 32 : ℚ) : ℝ) ≤ ((69458003518935 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((17364500879733 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((1297 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1027 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1297 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1027 / 96 : ℚ) : ℝ) ≤ ((69458003518935 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2594 : ((67492133 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((1297 / 32 : ℚ) : ℝ) ∧
    logKernel ((1297 / 32 : ℚ) : ℝ) ≤ ((134984271 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2594
  constructor
  · exact (show ((67492133 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((17364500879733 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1297 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((69458003518935 / 18446744073709551616 : ℚ) : ℝ) ≤ ((134984271 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2595 : ((34190578492949 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2595 / 64 : ℚ) : ℝ) ∧
    heightZ ((2595 / 64 : ℚ) : ℝ) ≤ ((68381156985901 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((34190578492949 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2595 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2057 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2595 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2057 / 192 : ℚ) : ℝ) ≤ ((68381156985901 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2595 : ((130831237 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2595 / 64 : ℚ) : ℝ) ∧
    logKernel ((2595 / 64 : ℚ) : ℝ) ≤ ((65415621 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2595
  constructor
  · exact (show ((130831237 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((34190578492949 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2595 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((68381156985901 / 18446744073709551616 : ℚ) : ℝ) ≤ ((65415621 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2596 : ((16830251352731 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((649 / 16 : ℚ) : ℝ) ∧
    heightZ ((649 / 16 : ℚ) : ℝ) ≤ ((67321005410927 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((16830251352731 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((649 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-515 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((649 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-515 / 48 : ℚ) : ℝ) ≤ ((67321005410927 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2596 : ((126805983 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((649 / 16 : ℚ) : ℝ) ∧
    logKernel ((649 / 16 : ℚ) : ℝ) ≤ ((31701497 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2596
  constructor
  · exact (show ((126805983 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((16830251352731 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((649 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((67321005410927 / 18446744073709551616 : ℚ) : ℝ) ≤ ((31701497 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2597 : ((16569322490669 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((2597 / 64 : ℚ) : ℝ) ∧
    heightZ ((2597 / 64 : ℚ) : ℝ) ≤ ((66277289962679 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((16569322490669 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((2597 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2063 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2597 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2063 / 192 : ℚ) : ℝ) ≤ ((66277289962679 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2597 : ((122904573 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2597 / 64 : ℚ) : ℝ) ∧
    logKernel ((2597 / 64 : ℚ) : ℝ) ≤ ((61452289 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2597
  constructor
  · exact (show ((122904573 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((16569322490669 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2597 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((66277289962679 / 18446744073709551616 : ℚ) : ℝ) ≤ ((61452289 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2598 : ((65249755822629 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1299 / 32 : ℚ) : ℝ) ∧
    heightZ ((1299 / 32 : ℚ) : ℝ) ≤ ((8156219477829 / 2305843009213693952 : ℚ) : ℝ) := by
  have h : ((65249755822629 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1299 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1033 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1299 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1033 / 96 : ℚ) : ℝ) ≤ ((8156219477829 / 2305843009213693952 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2598 : ((119123197 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1299 / 32 : ℚ) : ℝ) ∧
    logKernel ((1299 / 32 : ℚ) : ℝ) ≤ ((59561601 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2598
  constructor
  · exact (show ((119123197 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((65249755822629 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1299 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((8156219477829 / 2305843009213693952 : ℚ) : ℝ) ≤ ((59561601 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2599 : ((64238152122851 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2599 / 64 : ℚ) : ℝ) ∧
    heightZ ((2599 / 64 : ℚ) : ℝ) ≤ ((32119076061427 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((64238152122851 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2599 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2069 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2599 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2069 / 192 : ℚ) : ℝ) ≤ ((32119076061427 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2599 : ((115458161 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2599 / 64 : ℚ) : ℝ) ∧
    logKernel ((2599 / 64 : ℚ) : ℝ) ≤ ((57729083 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2599
  constructor
  · exact (show ((115458161 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((64238152122851 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2599 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((32119076061427 / 9223372036854775808 : ℚ) : ℝ) ≤ ((57729083 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2600 : ((31621115942379 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((325 / 8 : ℚ) : ℝ) ∧
    heightZ ((325 / 8 : ℚ) : ℝ) ≤ ((63242231884761 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((31621115942379 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((325 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-259 / 24 : ℚ) : ℝ) ∧
      Real.exp (-((325 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-259 / 24 : ℚ) : ℝ) ≤ ((63242231884761 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2600 : ((111905887 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((325 / 8 : ℚ) : ℝ) ∧
    logKernel ((325 / 8 : ℚ) : ℝ) ≤ ((27976473 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2600
  constructor
  · exact (show ((111905887 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((31621115942379 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((325 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((63242231884761 / 18446744073709551616 : ℚ) : ℝ) ≤ ((27976473 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2601 : ((31130875979407 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2601 / 64 : ℚ) : ℝ) ∧
    heightZ ((2601 / 64 : ℚ) : ℝ) ≤ ((62261751958817 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((31130875979407 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2601 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2075 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2601 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2075 / 192 : ℚ) : ℝ) ≤ ((62261751958817 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2601 : ((108462905 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2601 / 64 : ℚ) : ℝ) ∧
    logKernel ((2601 / 64 : ℚ) : ℝ) ≤ ((54231455 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2601
  constructor
  · exact (show ((108462905 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((31130875979407 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2601 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((62261751958817 / 18446744073709551616 : ℚ) : ℝ) ≤ ((54231455 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2602 : ((61296472965167 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1301 / 32 : ℚ) : ℝ) ∧
    heightZ ((1301 / 32 : ℚ) : ℝ) ≤ ((30648236482585 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((61296472965167 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1301 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1039 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1301 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1039 / 96 : ℚ) : ℝ) ≤ ((30648236482585 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2602 : ((26281463 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((1301 / 32 : ℚ) : ℝ) ∧
    logKernel ((1301 / 32 : ℚ) : ℝ) ≤ ((105125857 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2602
  constructor
  · exact (show ((26281463 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((61296472965167 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1301 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((30648236482585 / 9223372036854775808 : ℚ) : ℝ) ≤ ((105125857 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2603 : ((60346159235205 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2603 / 64 : ℚ) : ℝ) ∧
    heightZ ((2603 / 64 : ℚ) : ℝ) ≤ ((7543269904401 / 2305843009213693952 : ℚ) : ℝ) := by
  have h : ((60346159235205 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2603 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2081 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2603 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2081 / 192 : ℚ) : ℝ) ≤ ((7543269904401 / 2305843009213693952 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2603 : ((101891469 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2603 / 64 : ℚ) : ℝ) ∧
    logKernel ((2603 / 64 : ℚ) : ℝ) ≤ ((50945737 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2603
  constructor
  · exact (show ((101891469 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((60346159235205 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2603 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((7543269904401 / 2305843009213693952 : ℚ) : ℝ) ≤ ((50945737 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2604 : ((59410578754021 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((651 / 16 : ℚ) : ℝ) ∧
    heightZ ((651 / 16 : ℚ) : ℝ) ≤ ((7426322344253 / 2305843009213693952 : ℚ) : ℝ) := by
  have h : ((59410578754021 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((651 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-521 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((651 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-521 / 48 : ℚ) : ℝ) ≤ ((7426322344253 / 2305843009213693952 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2604 : ((49378299 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((651 / 16 : ℚ) : ℝ) ∧
    logKernel ((651 / 16 : ℚ) : ℝ) ≤ ((98756603 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2604
  constructor
  · exact (show ((49378299 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((59410578754021 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((651 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((7426322344253 / 2305843009213693952 : ℚ) : ℝ) ≤ ((98756603 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2605 : ((58489503103763 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2605 / 64 : ℚ) : ℝ) ∧
    heightZ ((2605 / 64 : ℚ) : ℝ) ≤ ((29244751551883 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((58489503103763 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2605 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2087 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2605 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2087 / 192 : ℚ) : ℝ) ≤ ((29244751551883 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2605 : ((95718177 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2605 / 64 : ℚ) : ℝ) ∧
    logKernel ((2605 / 64 : ℚ) : ℝ) ≤ ((47859091 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2605
  constructor
  · exact (show ((95718177 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((58489503103763 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2605 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((29244751551883 / 9223372036854775808 : ℚ) : ℝ) ≤ ((47859091 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2606 : ((57582707407871 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1303 / 32 : ℚ) : ℝ) ∧
    heightZ ((1303 / 32 : ℚ) : ℝ) ≤ ((28791353703937 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((57582707407871 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1303 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1045 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1303 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1045 / 96 : ℚ) : ℝ) ≤ ((28791353703937 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2606 : ((46386619 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((1303 / 32 : ℚ) : ℝ) ∧
    logKernel ((1303 / 32 : ℚ) : ℝ) ≤ ((92773243 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2606
  constructor
  · exact (show ((46386619 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((57582707407871 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1303 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((28791353703937 / 9223372036854775808 : ℚ) : ℝ) ≤ ((92773243 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2607 : ((28344985138087 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2607 / 64 : ℚ) : ℝ) ∧
    heightZ ((2607 / 64 : ℚ) : ℝ) ≤ ((56689970276177 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((28344985138087 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2607 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2093 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2607 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2093 / 192 : ℚ) : ℝ) ≤ ((56689970276177 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2607 : ((44959453 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2607 / 64 : ℚ) : ℝ) ∧
    logKernel ((2607 / 64 : ℚ) : ℝ) ≤ ((89918911 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2607
  constructor
  · exact (show ((44959453 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((28344985138087 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2607 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((56689970276177 / 18446744073709551616 : ℚ) : ℝ) ≤ ((89918911 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2608 : ((13952768437709 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((163 / 4 : ℚ) : ℝ) ∧
    heightZ ((163 / 4 : ℚ) : ℝ) ≤ ((55811073750839 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((13952768437709 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((163 / 4 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-131 / 12 : ℚ) : ℝ) ∧
      Real.exp (-((163 / 4 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-131 / 12 : ℚ) : ℝ) ≤ ((55811073750839 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2608 : ((10894049 / 9007199254740992 : ℚ) : ℝ) ≤ logKernel ((163 / 4 : ℚ) : ℝ) ∧
    logKernel ((163 / 4 : ℚ) : ℝ) ≤ ((87152397 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2608
  constructor
  · exact (show ((10894049 / 9007199254740992 : ℚ) : ℝ) ≤ zKernel ((13952768437709 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((163 / 4 : ℚ) : ℝ)) hh).trans
      (show zKernel ((55811073750839 / 18446744073709551616 : ℚ) : ℝ) ≤ ((87152397 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2609 : ((6868225406643 / 2305843009213693952 : ℚ) : ℝ) ≤ heightZ ((2609 / 64 : ℚ) : ℝ) ∧
    heightZ ((2609 / 64 : ℚ) : ℝ) ≤ ((54945803253147 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((6868225406643 / 2305843009213693952 : ℚ) : ℝ) ≤ Real.exp (-((2609 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2099 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2609 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2099 / 192 : ℚ) : ℝ) ≤ ((54945803253147 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2609 : ((42235497 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2609 / 64 : ℚ) : ℝ) ∧
    logKernel ((2609 / 64 : ℚ) : ℝ) ≤ ((84470999 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2609
  constructor
  · exact (show ((42235497 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((6868225406643 / 2305843009213693952 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2609 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((54945803253147 / 18446744073709551616 : ℚ) : ℝ) ≤ ((84470999 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem log_height_bounds_736 : ((266316660214269943 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1289 / 32 : ℚ) : ℝ) ∧
    Real.log ((1289 / 32 : ℚ) : ℝ) ≤ ((133158330107134973 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((266316660214269943 / 72057594037927936 : ℚ) : ℝ) ≤ ((1289 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1289 / 32 : ℚ) : ℝ) ≤ Real.exp ((133158330107134973 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_736 : heightPower (736 : Fin 988) ≤ ((3331681686247177 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_736
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_736 : heightFactor (736 : Fin 988) ≤ ((578770647 / 35184372088832 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_736
  obtain ⟨hpl, hph⟩ := kernel_bounds_2577
  obtain ⟨hcl, hch⟩ := kernel_bounds_2578
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2578
  have h : (((1661521 / 512 : ℚ) : ℝ) * (logKernel ((2577 / 64 : ℚ) : ℝ) - logKernel ((1289 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1289 / 32 : ℚ) : ℝ) + Real.log ((1289 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((578770647 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_737 : ((266344605762046203 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2579 / 64 : ℚ) : ℝ) ∧
    Real.log ((2579 / 64 : ℚ) : ℝ) ≤ ((133172302881023103 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((266344605762046203 / 72057594037927936 : ℚ) : ℝ) ≤ ((2579 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2579 / 64 : ℚ) : ℝ) ≤ Real.exp ((133172302881023103 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_737 : heightPower (737 : Fin 988) ≤ ((1668094447527141 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_737
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_737 : heightFactor (737 : Fin 988) ≤ ((4515230127 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_737
  obtain ⟨hpl, hph⟩ := kernel_bounds_2578
  obtain ⟨hcl, hch⟩ := kernel_bounds_2579
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2579
  have h : (((6651241 / 2048 : ℚ) : ℝ) * (logKernel ((1289 / 32 : ℚ) : ℝ) - logKernel ((2579 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2579 / 64 : ℚ) : ℝ) + Real.log ((2579 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((4515230127 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_738 : ((266372540476114971 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((645 / 16 : ℚ) : ℝ) ∧
    Real.log ((645 / 16 : ℚ) : ℝ) ≤ ((133186270238057487 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((266372540476114971 / 72057594037927936 : ℚ) : ℝ) ≤ ((645 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((645 / 16 : ℚ) : ℝ) ≤ Real.exp ((133186270238057487 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_738 : heightPower (738 : Fin 988) ≤ ((1670348030771109 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_738
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_738 : heightFactor (738 : Fin 988) ≤ ((4403146619 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_738
  obtain ⟨hpl, hph⟩ := kernel_bounds_2579
  obtain ⟨hcl, hch⟩ := kernel_bounds_2580
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2580
  have h : (((416025 / 128 : ℚ) : ℝ) * (logKernel ((2579 / 64 : ℚ) : ℝ) - logKernel ((645 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((645 / 16 : ℚ) : ℝ) + Real.log ((645 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((4403146619 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_739 : ((133200232182436421 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2581 / 64 : ℚ) : ℝ) ∧
    Real.log ((2581 / 64 : ℚ) : ℝ) ≤ ((266400464364872845 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((133200232182436421 / 36028797018963968 : ℚ) : ℝ) ≤ ((2581 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2581 / 64 : ℚ) : ℝ) ≤ Real.exp ((266400464364872845 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_739 : heightPower (739 : Fin 988) ≤ ((1672601592871891 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_739
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_739 : heightFactor (739 : Fin 988) ≤ ((4293843943 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_739
  obtain ⟨hpl, hph⟩ := kernel_bounds_2580
  obtain ⟨hcl, hch⟩ := kernel_bounds_2581
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2581
  have h : (((6661561 / 2048 : ℚ) : ℝ) * (logKernel ((645 / 16 : ℚ) : ℝ) - logKernel ((2581 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2581 / 64 : ℚ) : ℝ) + Real.log ((2581 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((4293843943 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_740 : ((8325886794897083 / 2251799813685248 : ℚ) : ℝ) ≤ Real.log ((1291 / 32 : ℚ) : ℝ) ∧
    Real.log ((1291 / 32 : ℚ) : ℝ) ≤ ((266428377436706659 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((8325886794897083 / 2251799813685248 : ℚ) : ℝ) ≤ ((1291 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1291 / 32 : ℚ) : ℝ) ≤ Real.exp ((266428377436706659 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_740 : heightPower (740 : Fin 988) ≤ ((3349710267691737 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_740
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_740 : heightFactor (740 : Fin 988) ≤ ((4187253145 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_740
  obtain ⟨hpl, hph⟩ := kernel_bounds_2581
  obtain ⟨hcl, hch⟩ := kernel_bounds_2582
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2582
  have h : (((1666681 / 512 : ℚ) : ℝ) * (logKernel ((2581 / 64 : ℚ) : ℝ) - logKernel ((1291 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1291 / 32 : ℚ) : ℝ) + Real.log ((1291 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((4187253145 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_741 : ((133228139849996753 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2583 / 64 : ℚ) : ℝ) ∧
    Real.log ((2583 / 64 : ℚ) : ℝ) ≤ ((266456279699993509 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((133228139849996753 / 36028797018963968 : ℚ) : ℝ) ≤ ((2583 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2583 / 64 : ℚ) : ℝ) ≤ Real.exp ((266456279699993509 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_741 : heightPower (741 : Fin 988) ≤ ((3354217307418805 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_741
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_741 : heightFactor (741 : Fin 988) ≤ ((2041653489 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_741
  obtain ⟨hpl, hph⟩ := kernel_bounds_2582
  obtain ⟨hcl, hch⟩ := kernel_bounds_2583
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2583
  have h : (((6671889 / 2048 : ℚ) : ℝ) * (logKernel ((1291 / 32 : ℚ) : ℝ) - logKernel ((2583 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2583 / 64 : ℚ) : ℝ) + Real.log ((2583 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((2041653489 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_742 : ((133242085581550381 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((323 / 8 : ℚ) : ℝ) ∧
    Real.log ((323 / 8 : ℚ) : ℝ) ≤ ((266484171163100765 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((133242085581550381 / 36028797018963968 : ℚ) : ℝ) ≤ ((323 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((323 / 8 : ℚ) : ℝ) ≤ Real.exp ((266484171163100765 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_742 : heightPower (742 : Fin 988) ≤ ((419840538119709 / 35184372088832 : ℚ) : ℝ) := by
  have hh := log_height_bounds_742
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_742 : heightFactor (742 : Fin 988) ≤ ((3981939863 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_742
  obtain ⟨hpl, hph⟩ := kernel_bounds_2583
  obtain ⟨hcl, hch⟩ := kernel_bounds_2584
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2584
  have h : (((104329 / 32 : ℚ) : ℝ) * (logKernel ((2583 / 64 : ℚ) : ℝ) - logKernel ((323 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((323 / 8 : ℚ) : ℝ) + Real.log ((323 / 8 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((3981939863 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_743 : ((266512051834386077 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2585 / 64 : ℚ) : ℝ) ∧
    Real.log ((2585 / 64 : ℚ) : ℝ) ≤ ((8328501619824565 / 2251799813685248 : ℚ) : ℝ) := by
  have hl : Real.exp ((266512051834386077 / 72057594037927936 : ℚ) : ℝ) ≤ ((2585 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2585 / 64 : ℚ) : ℝ) ≤ Real.exp ((8328501619824565 / 2251799813685248 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_743 : heightPower (743 : Fin 988) ≤ ((420403907542623 / 35184372088832 : ℚ) : ℝ) := by
  have hh := log_height_bounds_743
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_743 : heightFactor (743 : Fin 988) ≤ ((1941543923 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_743
  obtain ⟨hpl, hph⟩ := kernel_bounds_2584
  obtain ⟨hcl, hch⟩ := kernel_bounds_2585
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2585
  have h : (((6682225 / 2048 : ℚ) : ℝ) * (logKernel ((323 / 8 : ℚ) : ℝ) - logKernel ((2585 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2585 / 64 : ℚ) : ℝ) + Real.log ((2585 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1941543923 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_744 : ((266539921722197411 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1293 / 32 : ℚ) : ℝ) ∧
    Real.log ((1293 / 32 : ℚ) : ℝ) ≤ ((133269960861098707 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((266539921722197411 / 72057594037927936 : ℚ) : ℝ) ≤ ((1293 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1293 / 32 : ℚ) : ℝ) ≤ Real.exp ((133269960861098707 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_744 : heightPower (744 : Fin 988) ≤ ((3367738173601351 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_744
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_744 : heightFactor (744 : Fin 988) ≤ ((1893344279 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_744
  obtain ⟨hpl, hph⟩ := kernel_bounds_2585
  obtain ⟨hcl, hch⟩ := kernel_bounds_2586
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2586
  have h : (((1671849 / 512 : ℚ) : ℝ) * (logKernel ((2585 / 64 : ℚ) : ℝ) - logKernel ((1293 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1293 / 32 : ℚ) : ℝ) + Real.log ((1293 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1893344279 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_745 : ((133283890417436519 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2587 / 64 : ℚ) : ℝ) ∧
    Real.log ((2587 / 64 : ℚ) : ℝ) ≤ ((266567780834873041 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((133283890417436519 / 36028797018963968 : ℚ) : ℝ) ≤ ((2587 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2587 / 64 : ℚ) : ℝ) ≤ Real.exp ((266567780834873041 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_745 : heightPower (745 : Fin 988) ≤ ((210765315298209 / 17592186044416 : ℚ) : ℝ) := by
  have hh := log_height_bounds_745
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_745 : heightFactor (745 : Fin 988) ≤ ((1846340587 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_745
  obtain ⟨hpl, hph⟩ := kernel_bounds_2586
  obtain ⟨hcl, hch⟩ := kernel_bounds_2587
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2587
  have h : (((6692569 / 2048 : ℚ) : ℝ) * (logKernel ((1293 / 32 : ℚ) : ℝ) - logKernel ((2587 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2587 / 64 : ℚ) : ℝ) + Real.log ((2587 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1846340587 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_746 : ((266595629180741565 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((647 / 16 : ℚ) : ℝ) ∧
    Real.log ((647 / 16 : ℚ) : ℝ) ≤ ((4165556705949087 / 1125899906842624 : ℚ) : ℝ) := by
  have hl : Real.exp ((266595629180741565 / 72057594037927936 : ℚ) : ℝ) ≤ ((647 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((647 / 16 : ℚ) : ℝ) ≤ Real.exp ((4165556705949087 / 1125899906842624 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_746 : heightPower (746 : Fin 988) ≤ ((3376751873883497 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_746
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_746 : heightFactor (746 : Fin 988) ≤ ((3601006379 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_746
  obtain ⟨hpl, hph⟩ := kernel_bounds_2587
  obtain ⟨hcl, hch⟩ := kernel_bounds_2588
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2588
  have h : (((418609 / 128 : ℚ) : ℝ) * (logKernel ((2587 / 64 : ℚ) : ℝ) - logKernel ((647 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((647 / 16 : ℚ) : ℝ) + Real.log ((647 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((3601006379 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_747 : ((266623466768121949 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2589 / 64 : ℚ) : ℝ) ∧
    Real.log ((2589 / 64 : ℚ) : ℝ) ≤ ((8331983336503811 / 2251799813685248 : ℚ) : ℝ) := by
  have hl : Real.exp ((266623466768121949 / 72057594037927936 : ℚ) : ℝ) ≤ ((2589 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2589 / 64 : ℚ) : ℝ) ≤ Real.exp ((8331983336503811 / 2251799813685248 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_747 : heightPower (747 : Fin 988) ≤ ((1690629330485153 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_747
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_747 : heightFactor (747 : Fin 988) ≤ ((3511606327 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_747
  obtain ⟨hpl, hph⟩ := kernel_bounds_2588
  obtain ⟨hcl, hch⟩ := kernel_bounds_2589
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2589
  have h : (((6702921 / 2048 : ℚ) : ℝ) * (logKernel ((647 / 16 : ℚ) : ℝ) - logKernel ((2589 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2589 / 64 : ℚ) : ℝ) + Real.log ((2589 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((3511606327 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_748 : ((266651293605323505 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1295 / 32 : ℚ) : ℝ) ∧
    Real.log ((1295 / 32 : ℚ) : ℝ) ≤ ((66662823401330877 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((266651293605323505 / 72057594037927936 : ℚ) : ℝ) ≤ ((1295 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1295 / 32 : ℚ) : ℝ) ≤ Real.exp ((66662823401330877 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_748 : heightPower (748 : Fin 988) ≤ ((846441351516057 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_748
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_748 : heightFactor (748 : Fin 988) ≤ ((3424424605 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_748
  obtain ⟨hpl, hph⟩ := kernel_bounds_2589
  obtain ⟨hcl, hch⟩ := kernel_bounds_2590
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2590
  have h : (((1677025 / 512 : ℚ) : ℝ) * (logKernel ((2589 / 64 : ℚ) : ℝ) - logKernel ((1295 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1295 / 32 : ℚ) : ℝ) + Real.log ((1295 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((3424424605 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_749 : ((266679109700645929 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2591 / 64 : ℚ) : ℝ) ∧
    Real.log ((2591 / 64 : ℚ) : ℝ) ≤ ((66669777425161483 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((266679109700645929 / 72057594037927936 : ℚ) : ℝ) ≤ ((2591 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2591 / 64 : ℚ) : ℝ) ≤ Real.exp ((66669777425161483 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_749 : heightPower (749 : Fin 988) ≤ ((1695136054598843 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_749
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_749 : heightFactor (749 : Fin 988) ≤ ((417425775 / 35184372088832 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_749
  obtain ⟨hpl, hph⟩ := kernel_bounds_2590
  obtain ⟨hcl, hch⟩ := kernel_bounds_2591
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2591
  have h : (((6713281 / 2048 : ℚ) : ℝ) * (logKernel ((1295 / 32 : ℚ) : ℝ) - logKernel ((2591 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2591 / 64 : ℚ) : ℝ) + Real.log ((2591 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((417425775 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_750 : ((266706915062379307 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((81 / 2 : ℚ) : ℝ) ∧
    Real.log ((81 / 2 : ℚ) : ℝ) ≤ ((133353457531189655 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((266706915062379307 / 72057594037927936 : ℚ) : ℝ) ≤ ((81 / 2 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((81 / 2 : ℚ) : ℝ) ≤ Real.exp ((133353457531189655 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_750 : heightPower (750 : Fin 988) ≤ ((3394778770403061 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_750
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_750 : heightFactor (750 : Fin 988) ≤ ((3256497461 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_750
  obtain ⟨hpl, hph⟩ := kernel_bounds_2591
  obtain ⟨hcl, hch⟩ := kernel_bounds_2592
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2592
  have h : (((6561 / 2 : ℚ) : ℝ) * (logKernel ((2591 / 64 : ℚ) : ℝ) - logKernel ((81 / 2 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((81 / 2 : ℚ) : ℝ) + Real.log ((81 / 2 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((3256497461 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_751 : ((66683677424701033 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((2593 / 64 : ℚ) : ℝ) ∧
    Real.log ((2593 / 64 : ℚ) : ℝ) ≤ ((266734709698804135 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((66683677424701033 / 18014398509481984 : ℚ) : ℝ) ≤ ((2593 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2593 / 64 : ℚ) : ℝ) ≤ Real.exp ((266734709698804135 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_751 : heightPower (751 : Fin 988) ≤ ((3399285389712699 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_751
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_751 : heightFactor (751 : Fin 988) ≤ ((1587823033 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_751
  obtain ⟨hpl, hph⟩ := kernel_bounds_2592
  obtain ⟨hcl, hch⟩ := kernel_bounds_2593
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2593
  have h : (((6723649 / 2048 : ℚ) : ℝ) * (logKernel ((81 / 2 : ℚ) : ℝ) - logKernel ((2593 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2593 / 64 : ℚ) : ℝ) + Real.log ((2593 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1587823033 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_752 : ((266762493618191319 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1297 / 32 : ℚ) : ℝ) ∧
    Real.log ((1297 / 32 : ℚ) : ℝ) ≤ ((133381246809095661 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((266762493618191319 / 72057594037927936 : ℚ) : ℝ) ≤ ((1297 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1297 / 32 : ℚ) : ℝ) ≤ Real.exp ((133381246809095661 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_752 : heightPower (752 : Fin 988) ≤ ((3403791967158909 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_752
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_752 : heightFactor (752 : Fin 988) ≤ ((3096800993 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_752
  obtain ⟨hpl, hph⟩ := kernel_bounds_2593
  obtain ⟨hcl, hch⟩ := kernel_bounds_2594
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2594
  have h : (((1682209 / 512 : ℚ) : ℝ) * (logKernel ((2593 / 64 : ℚ) : ℝ) - logKernel ((1297 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1297 / 32 : ℚ) : ℝ) + Real.log ((1297 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((3096800993 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_753 : ((66697566707200555 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((2595 / 64 : ℚ) : ℝ) ∧
    Real.log ((2595 / 64 : ℚ) : ℝ) ≤ ((266790266828802223 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((66697566707200555 / 18014398509481984 : ℚ) : ℝ) ≤ ((2595 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2595 / 64 : ℚ) : ℝ) ≤ Real.exp ((266790266828802223 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_753 : heightPower (753 : Fin 988) ≤ ((1704149251386981 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_753
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_753 : heightFactor (753 : Fin 988) ≤ ((1509956241 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_753
  obtain ⟨hpl, hph⟩ := kernel_bounds_2594
  obtain ⟨hcl, hch⟩ := kernel_bounds_2595
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2595
  have h : (((6734025 / 2048 : ℚ) : ℝ) * (logKernel ((1297 / 32 : ℚ) : ℝ) - logKernel ((2595 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2595 / 64 : ℚ) : ℝ) + Real.log ((2595 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1509956241 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_754 : ((66704507334722159 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((649 / 16 : ℚ) : ℝ) ∧
    Real.log ((649 / 16 : ℚ) : ℝ) ≤ ((266818029338888639 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((66704507334722159 / 18014398509481984 : ℚ) : ℝ) ≤ ((649 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((649 / 16 : ℚ) : ℝ) ≤ Real.exp ((266818029338888639 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_754 : heightPower (754 : Fin 988) ≤ ((3412804996590091 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_754
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_754 : heightFactor (754 : Fin 988) ≤ ((2944932007 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_754
  obtain ⟨hpl, hph⟩ := kernel_bounds_2595
  obtain ⟨hcl, hch⟩ := kernel_bounds_2596
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2596
  have h : (((421201 / 128 : ℚ) : ℝ) * (logKernel ((2595 / 64 : ℚ) : ℝ) - logKernel ((649 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((649 / 16 : ℚ) : ℝ) + Real.log ((649 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((2944932007 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_755 : ((133422890578346419 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2597 / 64 : ℚ) : ℝ) ∧
    Real.log ((2597 / 64 : ℚ) : ℝ) ≤ ((266845781156692841 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((133422890578346419 / 36028797018963968 : ℚ) : ℝ) ≤ ((2597 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2597 / 64 : ℚ) : ℝ) ≤ Real.exp ((266845781156692841 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_755 : heightPower (755 : Fin 988) ≤ ((3417311448639493 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_755
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_755 : heightFactor (755 : Fin 988) ≤ ((2871812245 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_755
  obtain ⟨hpl, hph⟩ := kernel_bounds_2596
  obtain ⟨hcl, hch⟩ := kernel_bounds_2597
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2597
  have h : (((6744409 / 2048 : ℚ) : ℝ) * (logKernel ((649 / 16 : ℚ) : ℝ) - logKernel ((2597 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2597 / 64 : ℚ) : ℝ) + Real.log ((2597 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((2871812245 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_756 : ((66718380572611893 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((1299 / 32 : ℚ) : ℝ) ∧
    Real.log ((1299 / 32 : ℚ) : ℝ) ≤ ((266873522290447575 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((66718380572611893 / 18014398509481984 : ℚ) : ℝ) ≤ ((1299 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1299 / 32 : ℚ) : ℝ) ≤ Real.exp ((266873522290447575 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_756 : heightPower (756 : Fin 988) ≤ ((1710908929477163 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_756
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_756 : heightFactor (756 : Fin 988) ≤ ((2800507047 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_756
  obtain ⟨hpl, hph⟩ := kernel_bounds_2597
  obtain ⟨hcl, hch⟩ := kernel_bounds_2598
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2598
  have h : (((1687401 / 512 : ℚ) : ℝ) * (logKernel ((2597 / 64 : ℚ) : ℝ) - logKernel ((1299 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1299 / 32 : ℚ) : ℝ) + Real.log ((1299 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((2800507047 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_757 : ((66725313187094021 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((2599 / 64 : ℚ) : ℝ) ∧
    Real.log ((2599 / 64 : ℚ) : ℝ) ≤ ((266901252748376087 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((66725313187094021 / 18014398509481984 : ℚ) : ℝ) ≤ ((2599 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2599 / 64 : ℚ) : ℝ) ≤ Real.exp ((266901252748376087 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_757 : heightPower (757 : Fin 988) ≤ ((1713162113783357 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_757
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_757 : heightFactor (757 : Fin 988) ≤ ((2730971405 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_757
  obtain ⟨hpl, hph⟩ := kernel_bounds_2598
  obtain ⟨hcl, hch⟩ := kernel_bounds_2599
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2599
  have h : (((6754801 / 2048 : ℚ) : ℝ) * (logKernel ((1299 / 32 : ℚ) : ℝ) - logKernel ((2599 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2599 / 64 : ℚ) : ℝ) + Real.log ((2599 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((2730971405 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_758 : ((266928972538692127 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((325 / 8 : ℚ) : ℝ) ∧
    Real.log ((325 / 8 : ℚ) : ℝ) ≤ ((133464486269346065 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((266928972538692127 / 72057594037927936 : ℚ) : ℝ) ≤ ((325 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((325 / 8 : ℚ) : ℝ) ≤ Real.exp ((133464486269346065 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_758 : heightPower (758 : Fin 988) ≤ ((857707638627185 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_758
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_758 : heightFactor (758 : Fin 988) ≤ ((2663161431 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_758
  obtain ⟨hpl, hph⟩ := kernel_bounds_2599
  obtain ⟨hcl, hch⟩ := kernel_bounds_2600
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2600
  have h : (((105625 / 32 : ℚ) : ℝ) * (logKernel ((2599 / 64 : ℚ) : ℝ) - logKernel ((325 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((325 / 8 : ℚ) : ℝ) + Real.log ((325 / 8 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((2663161431 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_759 : ((266956681669599979 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2601 / 64 : ℚ) : ℝ) ∧
    Real.log ((2601 / 64 : ℚ) : ℝ) ≤ ((133478340834799991 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((266956681669599979 / 72057594037927936 : ℚ) : ℝ) ≤ ((2601 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2601 / 64 : ℚ) : ℝ) ≤ Real.exp ((133478340834799991 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_759 : heightPower (759 : Fin 988) ≤ ((858834209953113 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_759
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_759 : heightFactor (759 : Fin 988) ≤ ((2597034321 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_759
  obtain ⟨hpl, hph⟩ := kernel_bounds_2600
  obtain ⟨hcl, hch⟩ := kernel_bounds_2601
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2601
  have h : (((6765201 / 2048 : ℚ) : ℝ) * (logKernel ((325 / 8 : ℚ) : ℝ) - logKernel ((2601 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2601 / 64 : ℚ) : ℝ) + Real.log ((2601 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((2597034321 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_760 : ((133492190074647229 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((1301 / 32 : ℚ) : ℝ) ∧
    Real.log ((1301 / 32 : ℚ) : ℝ) ≤ ((266984380149294461 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((133492190074647229 / 36028797018963968 : ℚ) : ℝ) ≤ ((1301 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1301 / 32 : ℚ) : ℝ) ≤ Real.exp ((266984380149294461 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_760 : heightPower (760 : Fin 988) ≤ ((3439843083509863 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_760
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_760 : heightFactor (760 : Fin 988) ≤ ((1266274167 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_760
  obtain ⟨hpl, hph⟩ := kernel_bounds_2601
  obtain ⟨hcl, hch⟩ := kernel_bounds_2602
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2602
  have h : (((1692601 / 512 : ℚ) : ℝ) * (logKernel ((2601 / 64 : ℚ) : ℝ) - logKernel ((1301 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1301 / 32 : ℚ) : ℝ) + Real.log ((1301 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1266274167 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_761 : ((267012067985960935 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2603 / 64 : ℚ) : ℝ) ∧
    Real.log ((2603 / 64 : ℚ) : ℝ) ≤ ((133506033992980469 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((267012067985960935 / 72057594037927936 : ℚ) : ℝ) ≤ ((2603 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2603 / 64 : ℚ) : ℝ) ≤ Real.exp ((133506033992980469 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_761 : heightPower (761 : Fin 988) ≤ ((3444349285632945 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_761
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_761 : heightFactor (761 : Fin 988) ≤ ((617415691 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_761
  obtain ⟨hpl, hph⟩ := kernel_bounds_2602
  obtain ⟨hcl, hch⟩ := kernel_bounds_2603
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2603
  have h : (((6775609 / 2048 : ℚ) : ℝ) * (logKernel ((1301 / 32 : ℚ) : ℝ) - logKernel ((2603 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2603 / 64 : ℚ) : ℝ) + Real.log ((2603 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((617415691 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_762 : ((267039745187775349 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((651 / 16 : ℚ) : ℝ) ∧
    Real.log ((651 / 16 : ℚ) : ℝ) ≤ ((33379968148471919 / 9007199254740992 : ℚ) : ℝ) := by
  have hl : Real.exp ((267039745187775349 / 72057594037927936 : ℚ) : ℝ) ≤ ((651 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((651 / 16 : ℚ) : ℝ) ≤ Real.exp ((33379968148471919 / 9007199254740992 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_762 : heightPower (762 : Fin 988) ≤ ((3448855446213637 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_762
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_762 : heightFactor (762 : Fin 988) ≤ ((1204168957 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_762
  obtain ⟨hpl, hph⟩ := kernel_bounds_2603
  obtain ⟨hcl, hch⟩ := kernel_bounds_2604
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2604
  have h : (((423801 / 128 : ℚ) : ℝ) * (logKernel ((2603 / 64 : ℚ) : ℝ) - logKernel ((651 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((651 / 16 : ℚ) : ℝ) + Real.log ((651 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1204168957 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_763 : ((66766852940726055 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((2605 / 64 : ℚ) : ℝ) ∧
    Real.log ((2605 / 64 : ℚ) : ℝ) ≤ ((267067411762904223 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((66766852940726055 / 18014398509481984 : ℚ) : ℝ) ≤ ((2605 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2605 / 64 : ℚ) : ℝ) ≤ Real.exp ((267067411762904223 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_763 : heightPower (763 : Fin 988) ≤ ((1726680782641919 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_763
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_763 : heightFactor (763 : Fin 988) ≤ ((2348535069 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_763
  obtain ⟨hpl, hph⟩ := kernel_bounds_2604
  obtain ⟨hcl, hch⟩ := kernel_bounds_2605
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2605
  have h : (((6786025 / 2048 : ℚ) : ℝ) * (logKernel ((651 / 16 : ℚ) : ℝ) - logKernel ((2605 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2605 / 64 : ℚ) : ℝ) + Real.log ((2605 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((2348535069 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_764 : ((267095067719504667 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1303 / 32 : ℚ) : ℝ) ∧
    Real.log ((1303 / 32 : ℚ) : ℝ) ≤ ((133547533859752335 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((267095067719504667 / 72057594037927936 : ℚ) : ℝ) ≤ ((1303 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1303 / 32 : ℚ) : ℝ) ≤ Real.exp ((133547533859752335 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_764 : heightPower (764 : Fin 988) ≤ ((3457867642875413 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_764
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_764 : heightFactor (764 : Fin 988) ≤ ((572554119 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_764
  obtain ⟨hpl, hph⟩ := kernel_bounds_2605
  obtain ⟨hcl, hch⟩ := kernel_bounds_2606
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2606
  have h : (((1697809 / 512 : ℚ) : ℝ) * (logKernel ((2605 / 64 : ℚ) : ℝ) - logKernel ((1303 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1303 / 32 : ℚ) : ℝ) + Real.log ((1303 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((572554119 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_765 : ((267122713065724421 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2607 / 64 : ℚ) : ℝ) ∧
    Real.log ((2607 / 64 : ℚ) : ℝ) ≤ ((33390339133215553 / 9007199254740992 : ℚ) : ℝ) := by
  have hl : Real.exp ((267122713065724421 / 72057594037927936 : ℚ) : ℝ) ≤ ((2607 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2607 / 64 : ℚ) : ℝ) ≤ Real.exp ((33390339133215553 / 9007199254740992 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_765 : heightPower (765 : Fin 988) ≤ ((865593419755047 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_765
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_765 : heightFactor (765 : Fin 988) ≤ ((2233345319 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_765
  obtain ⟨hpl, hph⟩ := kernel_bounds_2606
  obtain ⟨hcl, hch⟩ := kernel_bounds_2607
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2607
  have h : (((6796449 / 2048 : ℚ) : ℝ) * (logKernel ((1303 / 32 : ℚ) : ℝ) - logKernel ((2607 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2607 / 64 : ℚ) : ℝ) + Real.log ((2607 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((2233345319 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_766 : ((267150347809701835 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((163 / 4 : ℚ) : ℝ) ∧
    Real.log ((163 / 4 : ℚ) : ℝ) ≤ ((133575173904850919 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((267150347809701835 / 72057594037927936 : ℚ) : ℝ) ≤ ((163 / 4 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((163 / 4 : ℚ) : ℝ) ≤ Real.exp ((133575173904850919 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_766 : heightPower (766 : Fin 988) ≤ ((3466879673749953 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_766
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_766 : heightFactor (766 : Fin 988) ≤ ((1088942845 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_766
  obtain ⟨hpl, hph⟩ := kernel_bounds_2607
  obtain ⟨hcl, hch⟩ := kernel_bounds_2608
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2608
  have h : (((26569 / 8 : ℚ) : ℝ) * (logKernel ((2607 / 64 : ℚ) : ℝ) - logKernel ((163 / 4 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((163 / 4 : ℚ) : ℝ) + Real.log ((163 / 4 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1088942845 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_767 : ((66794492989891477 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((2609 / 64 : ℚ) : ℝ) ∧
    Real.log ((2609 / 64 : ℚ) : ℝ) ≤ ((267177971959565911 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((66794492989891477 / 18014398509481984 : ℚ) : ℝ) ≤ ((2609 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2609 / 64 : ℚ) : ℝ) ≤ Real.exp ((267177971959565911 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_767 : heightPower (767 : Fin 988) ≤ ((216961601693529 / 17592186044416 : ℚ) : ℝ) := by
  have hh := log_height_bounds_767
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_767 : heightFactor (767 : Fin 988) ≤ ((1061901289 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_767
  obtain ⟨hpl, hph⟩ := kernel_bounds_2608
  obtain ⟨hcl, hch⟩ := kernel_bounds_2609
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2609
  have h : (((6806881 / 2048 : ℚ) : ℝ) * (logKernel ((163 / 4 : ℚ) : ℝ) - logKernel ((2609 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2609 / 64 : ℚ) : ℝ) + Real.log ((2609 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1061901289 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

end LegendreK6.M2Pilot.Enclosures.Height023
