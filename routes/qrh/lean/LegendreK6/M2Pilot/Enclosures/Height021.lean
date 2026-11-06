import LegendreK6.M2PilotDefinitions
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp

/-! Generated proposals: every bound is checked by Lean, not by trusting Arb. -/
namespace LegendreK6.M2Pilot.Enclosures.Height021
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem height_z_bounds_2513 : ((123125002950283 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2513 / 64 : ℚ) : ℝ) ∧
    heightZ ((2513 / 64 : ℚ) : ℝ) ≤ ((246250005900569 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((123125002950283 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2513 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1811 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2513 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1811 / 192 : ℚ) : ℝ) ≤ ((246250005900569 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2513 : ((1696645325 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2513 / 64 : ℚ) : ℝ) ∧
    logKernel ((2513 / 64 : ℚ) : ℝ) ≤ ((848322665 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2513
  constructor
  · exact (show ((1696645325 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((123125002950283 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2513 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((246250005900569 / 18446744073709551616 : ℚ) : ℝ) ≤ ((848322665 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2514 : ((60608063355417 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((1257 / 32 : ℚ) : ℝ) ∧
    heightZ ((1257 / 32 : ℚ) : ℝ) ≤ ((242432253421671 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((60608063355417 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((1257 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-907 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1257 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-907 / 96 : ℚ) : ℝ) ≤ ((242432253421671 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2514 : ((411111259 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((1257 / 32 : ℚ) : ℝ) ∧
    logKernel ((1257 / 32 : ℚ) : ℝ) ≤ ((1644445041 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2514
  constructor
  · exact (show ((411111259 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((60608063355417 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1257 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((242432253421671 / 18446744073709551616 : ℚ) : ℝ) ≤ ((1644445041 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2515 : ((29834211213603 / 2305843009213693952 : ℚ) : ℝ) ≤ heightZ ((2515 / 64 : ℚ) : ℝ) ∧
    heightZ ((2515 / 64 : ℚ) : ℝ) ≤ ((238673689708827 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((29834211213603 / 2305843009213693952 : ℚ) : ℝ) ≤ Real.exp (-((2515 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1817 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2515 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1817 / 192 : ℚ) : ℝ) ≤ ((238673689708827 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2515 : ((1593850781 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2515 / 64 : ℚ) : ℝ) ∧
    logKernel ((2515 / 64 : ℚ) : ℝ) ≤ ((796925393 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2515
  constructor
  · exact (show ((1593850781 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((29834211213603 / 2305843009213693952 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2515 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((238673689708827 / 18446744073709551616 : ℚ) : ℝ) ≤ ((796925393 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2516 : ((29371674640659 / 2305843009213693952 : ℚ) : ℝ) ≤ heightZ ((629 / 16 : ℚ) : ℝ) ∧
    heightZ ((629 / 16 : ℚ) : ℝ) ≤ ((234973397125275 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((29371674640659 / 2305843009213693952 : ℚ) : ℝ) ≤ Real.exp (-((629 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-455 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((629 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-455 / 48 : ℚ) : ℝ) ≤ ((234973397125275 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2516 : ((386203287 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((629 / 16 : ℚ) : ℝ) ∧
    logKernel ((629 / 16 : ℚ) : ℝ) ≤ ((1544813153 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2516
  constructor
  · exact (show ((386203287 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((29371674640659 / 2305843009213693952 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((629 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((234973397125275 / 18446744073709551616 : ℚ) : ℝ) ≤ ((1544813153 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2517 : ((231330472260887 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2517 / 64 : ℚ) : ℝ) ∧
    heightZ ((2517 / 64 : ℚ) : ℝ) ≤ ((115665236130445 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((231330472260887 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2517 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1823 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2517 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1823 / 192 : ℚ) : ℝ) ≤ ((115665236130445 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2517 : ((374321061 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((2517 / 64 : ℚ) : ℝ) ∧
    logKernel ((2517 / 64 : ℚ) : ℝ) ≤ ((1497284249 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2517
  constructor
  · exact (show ((374321061 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((231330472260887 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2517 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((115665236130445 / 9223372036854775808 : ℚ) : ℝ) ≤ ((1497284249 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2518 : ((113872012855811 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((1259 / 32 : ℚ) : ℝ) ∧
    heightZ ((1259 / 32 : ℚ) : ℝ) ≤ ((227744025711625 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((113872012855811 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((1259 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-913 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1259 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-913 / 96 : ℚ) : ℝ) ≤ ((227744025711625 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2518 : ((1451217651 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1259 / 32 : ℚ) : ℝ) ∧
    logKernel ((1259 / 32 : ℚ) : ℝ) ≤ ((181402207 / 9007199254740992 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2518
  constructor
  · exact (show ((1451217651 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((113872012855811 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1259 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((227744025711625 / 18446744073709551616 : ℚ) : ℝ) ≤ ((181402207 / 9007199254740992 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2519 : ((28026647732795 / 2305843009213693952 : ℚ) : ℝ) ≤ heightZ ((2519 / 64 : ℚ) : ℝ) ∧
    heightZ ((2519 / 64 : ℚ) : ℝ) ≤ ((224213181862363 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((28026647732795 / 2305843009213693952 : ℚ) : ℝ) ≤ Real.exp (-((2519 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1829 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2519 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1829 / 192 : ℚ) : ℝ) ≤ ((224213181862363 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2519 : ((1406568377 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2519 / 64 : ℚ) : ℝ) ∧
    logKernel ((2519 / 64 : ℚ) : ℝ) ≤ ((703284191 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2519
  constructor
  · exact (show ((1406568377 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((28026647732795 / 2305843009213693952 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2519 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((224213181862363 / 18446744073709551616 : ℚ) : ℝ) ≤ ((703284191 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2520 : ((220737078673139 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((315 / 8 : ℚ) : ℝ) ∧
    heightZ ((315 / 8 : ℚ) : ℝ) ≤ ((110368539336571 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((220737078673139 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((315 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-229 / 24 : ℚ) : ℝ) ∧
      Real.exp (-((315 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-229 / 24 : ℚ) : ℝ) ≤ ((110368539336571 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2520 : ((681646409 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((315 / 8 : ℚ) : ℝ) ∧
    logKernel ((315 / 8 : ℚ) : ℝ) ≤ ((1363292823 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2520
  constructor
  · exact (show ((681646409 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((220737078673139 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((315 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((110368539336571 / 9223372036854775808 : ℚ) : ℝ) ≤ ((1363292823 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2521 : ((13582179216793 / 1152921504606846976 : ℚ) : ℝ) ≤ heightZ ((2521 / 64 : ℚ) : ℝ) ∧
    heightZ ((2521 / 64 : ℚ) : ℝ) ≤ ((217314867468691 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((13582179216793 / 1152921504606846976 : ℚ) : ℝ) ≤ Real.exp (-((2521 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1835 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2521 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1835 / 192 : ℚ) : ℝ) ≤ ((217314867468691 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2521 : ((1321348707 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2521 / 64 : ℚ) : ℝ) ∧
    logKernel ((2521 / 64 : ℚ) : ℝ) ≤ ((165168589 / 9007199254740992 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2521
  constructor
  · exact (show ((1321348707 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((13582179216793 / 1152921504606846976 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2521 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((217314867468691 / 18446744073709551616 : ℚ) : ℝ) ≤ ((165168589 / 9007199254740992 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2522 : ((213945712731225 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1261 / 32 : ℚ) : ℝ) ∧
    heightZ ((1261 / 32 : ℚ) : ℝ) ≤ ((53486428182807 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((213945712731225 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1261 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-919 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1261 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-919 / 96 : ℚ) : ℝ) ≤ ((53486428182807 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2522 : ((1280695081 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1261 / 32 : ℚ) : ℝ) ∧
    logKernel ((1261 / 32 : ℚ) : ℝ) ≤ ((640347543 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2522
  constructor
  · exact (show ((1280695081 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((213945712731225 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1261 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((53486428182807 / 4611686018427387904 : ℚ) : ℝ) ≤ ((640347543 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2523 : ((105314395948237 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2523 / 64 : ℚ) : ℝ) ∧
    heightZ ((2523 / 64 : ℚ) : ℝ) ≤ ((210628791896477 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((105314395948237 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2523 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1841 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2523 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1841 / 192 : ℚ) : ℝ) ≤ ((210628791896477 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2523 : ((310323059 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((2523 / 64 : ℚ) : ℝ) ∧
    logKernel ((2523 / 64 : ℚ) : ℝ) ≤ ((1241292241 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2523
  constructor
  · exact (show ((310323059 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((105314395948237 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2523 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((210628791896477 / 18446744073709551616 : ℚ) : ℝ) ≤ ((1241292241 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2524 : ((3240051486763 / 288230376151711744 : ℚ) : ℝ) ≤ heightZ ((631 / 16 : ℚ) : ℝ) ∧
    heightZ ((631 / 16 : ℚ) : ℝ) ≤ ((207363295152835 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((3240051486763 / 288230376151711744 : ℚ) : ℝ) ≤ Real.exp (-((631 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-461 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((631 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-461 / 48 : ℚ) : ℝ) ≤ ((207363295152835 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2524 : ((1203101689 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((631 / 16 : ℚ) : ℝ) ∧
    logKernel ((631 / 16 : ℚ) : ℝ) ≤ ((601550847 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2524
  constructor
  · exact (show ((1203101689 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((3240051486763 / 288230376151711744 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((631 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((207363295152835 / 18446744073709551616 : ℚ) : ℝ) ≤ ((601550847 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2525 : ((12759276577729 / 1152921504606846976 : ℚ) : ℝ) ≤ heightZ ((2525 / 64 : ℚ) : ℝ) ∧
    heightZ ((2525 / 64 : ℚ) : ℝ) ≤ ((204148425243667 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((12759276577729 / 1152921504606846976 : ℚ) : ℝ) ≤ Real.exp (-((2525 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1847 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2525 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1847 / 192 : ℚ) : ℝ) ≤ ((204148425243667 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2525 : ((1166086141 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2525 / 64 : ℚ) : ℝ) ∧
    logKernel ((2525 / 64 : ℚ) : ℝ) ≤ ((583043073 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2525
  constructor
  · exact (show ((1166086141 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((12759276577729 / 1152921504606846976 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2525 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((204148425243667 / 18446744073709551616 : ℚ) : ℝ) ≤ ((583043073 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2526 : ((50245849318163 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((1263 / 32 : ℚ) : ℝ) ∧
    heightZ ((1263 / 32 : ℚ) : ℝ) ≤ ((200983397272655 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((50245849318163 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((1263 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-925 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1263 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-925 / 96 : ℚ) : ℝ) ≤ ((200983397272655 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2526 : ((565104721 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((1263 / 32 : ℚ) : ℝ) ∧
    logKernel ((1263 / 32 : ℚ) : ℝ) ≤ ((1130209447 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2526
  constructor
  · exact (show ((565104721 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((50245849318163 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1263 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((200983397272655 / 18446744073709551616 : ℚ) : ℝ) ≤ ((1130209447 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2527 : ((197867438512169 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2527 / 64 : ℚ) : ℝ) ∧
    heightZ ((2527 / 64 : ℚ) : ℝ) ≤ ((49466859628043 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((197867438512169 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2527 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1853 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2527 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1853 / 192 : ℚ) : ℝ) ≤ ((49466859628043 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2527 : ((1095436553 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2527 / 64 : ℚ) : ℝ) ∧
    logKernel ((2527 / 64 : ℚ) : ℝ) ≤ ((547718279 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2527
  constructor
  · exact (show ((1095436553 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((197867438512169 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2527 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((49466859628043 / 4611686018427387904 : ℚ) : ℝ) ≤ ((547718279 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2528 : ((194799788214617 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((79 / 2 : ℚ) : ℝ) ∧
    heightZ ((79 / 2 : ℚ) : ℝ) ≤ ((48699947053655 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((194799788214617 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((79 / 2 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-29 / 3 : ℚ) : ℝ) ∧
      Real.exp (-((79 / 2 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-29 / 3 : ℚ) : ℝ) ≤ ((48699947053655 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2528 : ((530866757 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((79 / 2 : ℚ) : ℝ) ∧
    logKernel ((79 / 2 : ℚ) : ℝ) ≤ ((1061733519 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2528
  constructor
  · exact (show ((530866757 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((194799788214617 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((79 / 2 : ℚ) : ℝ)) hh).trans
      (show zKernel ((48699947053655 / 4611686018427387904 : ℚ) : ℝ) ≤ ((1061733519 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2529 : ((191779697426699 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2529 / 64 : ℚ) : ℝ) ∧
    heightZ ((2529 / 64 : ℚ) : ℝ) ≤ ((95889848713351 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((191779697426699 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2529 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1859 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2529 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1859 / 192 : ℚ) : ℝ) ≤ ((95889848713351 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2529 : ((1029067407 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2529 / 64 : ℚ) : ℝ) ∧
    logKernel ((2529 / 64 : ℚ) : ℝ) ≤ ((257266853 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2529
  constructor
  · exact (show ((1029067407 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((191779697426699 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2529 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((95889848713351 / 9223372036854775808 : ℚ) : ℝ) ≤ ((257266853 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2530 : ((5900200900205 / 576460752303423488 : ℚ) : ℝ) ≤ heightZ ((1265 / 32 : ℚ) : ℝ) ∧
    heightZ ((1265 / 32 : ℚ) : ℝ) ≤ ((188806428806563 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((5900200900205 / 576460752303423488 : ℚ) : ℝ) ≤ Real.exp (-((1265 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-931 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1265 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-931 / 96 : ℚ) : ℝ) ≤ ((188806428806563 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2530 : ((249351583 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((1265 / 32 : ℚ) : ℝ) ∧
    logKernel ((1265 / 32 : ℚ) : ℝ) ≤ ((997406337 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2530
  constructor
  · exact (show ((249351583 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((5900200900205 / 576460752303423488 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1265 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((188806428806563 / 18446744073709551616 : ℚ) : ℝ) ≤ ((997406337 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2531 : ((92939628221887 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2531 / 64 : ℚ) : ℝ) ∧
    heightZ ((2531 / 64 : ℚ) : ℝ) ≤ ((185879256443777 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((92939628221887 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2531 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1865 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2531 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1865 / 192 : ℚ) : ℝ) ≤ ((185879256443777 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2531 : ((966719365 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2531 / 64 : ℚ) : ℝ) ∧
    logKernel ((2531 / 64 : ℚ) : ℝ) ≤ ((483359685 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2531
  constructor
  · exact (show ((966719365 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((92939628221887 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2531 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((185879256443777 / 18446744073709551616 : ℚ) : ℝ) ≤ ((483359685 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2532 : ((91498732841055 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((633 / 16 : ℚ) : ℝ) ∧
    heightZ ((633 / 16 : ℚ) : ℝ) ≤ ((182997465682113 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((91498732841055 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((633 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-467 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((633 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-467 / 48 : ℚ) : ℝ) ≤ ((182997465682113 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2532 : ((936976537 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((633 / 16 : ℚ) : ℝ) ∧
    logKernel ((633 / 16 : ℚ) : ℝ) ≤ ((468488271 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2532
  constructor
  · exact (show ((936976537 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((91498732841055 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((633 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((182997465682113 / 18446744073709551616 : ℚ) : ℝ) ≤ ((468488271 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2533 : ((5630011029533 / 576460752303423488 : ℚ) : ℝ) ≤ heightZ ((2533 / 64 : ℚ) : ℝ) ∧
    heightZ ((2533 / 64 : ℚ) : ℝ) ≤ ((180160352945059 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((5630011029533 / 576460752303423488 : ℚ) : ℝ) ≤ Real.exp (-((2533 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1871 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2533 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1871 / 192 : ℚ) : ℝ) ≤ ((180160352945059 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2533 : ((908148799 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2533 / 64 : ℚ) : ℝ) ∧
    logKernel ((2533 / 64 : ℚ) : ℝ) ≤ ((227037201 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2533
  constructor
  · exact (show ((908148799 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((5630011029533 / 576460752303423488 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2533 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((180160352945059 / 18446744073709551616 : ℚ) : ℝ) ≤ ((227037201 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2534 : ((177367225564045 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1267 / 32 : ℚ) : ℝ) ∧
    heightZ ((1267 / 32 : ℚ) : ℝ) ≤ ((11085451597753 / 1152921504606846976 : ℚ) : ℝ) := by
  have h : ((177367225564045 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1267 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-937 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1267 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-937 / 96 : ℚ) : ℝ) ≤ ((11085451597753 / 1152921504606846976 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2534 : ((440103999 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((1267 / 32 : ℚ) : ℝ) ∧
    logKernel ((1267 / 32 : ℚ) : ℝ) ≤ ((880208003 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2534
  constructor
  · exact (show ((440103999 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((177367225564045 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1267 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((11085451597753 / 1152921504606846976 : ℚ) : ℝ) ≤ ((880208003 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2535 : ((174617401609337 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2535 / 64 : ℚ) : ℝ) ∧
    heightZ ((2535 / 64 : ℚ) : ℝ) ≤ ((43654350402335 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((174617401609337 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2535 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1877 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2535 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1877 / 192 : ℚ) : ℝ) ≤ ((43654350402335 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2535 : ((853126845 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2535 / 64 : ℚ) : ℝ) ∧
    logKernel ((2535 / 64 : ℚ) : ℝ) ≤ ((426563425 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2535
  constructor
  · exact (show ((853126845 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((174617401609337 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2535 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((43654350402335 / 4611686018427387904 : ℚ) : ℝ) ≤ ((426563425 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2536 : ((85955104861767 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((317 / 8 : ℚ) : ℝ) ∧
    heightZ ((317 / 8 : ℚ) : ℝ) ≤ ((171910209723537 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((85955104861767 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((317 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-235 / 24 : ℚ) : ℝ) ∧
      Real.exp (-((317 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-235 / 24 : ℚ) : ℝ) ≤ ((171910209723537 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2536 : ((826878891 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((317 / 8 : ℚ) : ℝ) ∧
    logKernel ((317 / 8 : ℚ) : ℝ) ≤ ((51679931 / 4503599627370496 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2536
  constructor
  · exact (show ((826878891 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((85955104861767 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((317 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((171910209723537 / 18446744073709551616 : ℚ) : ℝ) ≤ ((51679931 / 4503599627370496 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2537 : ((21155623619709 / 2305843009213693952 : ℚ) : ℝ) ≤ heightZ ((2537 / 64 : ℚ) : ℝ) ∧
    heightZ ((2537 / 64 : ℚ) : ℝ) ≤ ((169244988957675 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((21155623619709 / 2305843009213693952 : ℚ) : ℝ) ≤ Real.exp (-((2537 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1883 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2537 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1883 / 192 : ℚ) : ℝ) ≤ ((169244988957675 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2537 : ((400719251 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2537 / 64 : ℚ) : ℝ) ∧
    logKernel ((2537 / 64 : ℚ) : ℝ) ≤ ((801438507 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2537
  constructor
  · exact (show ((400719251 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((21155623619709 / 2305843009213693952 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2537 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((169244988957675 / 18446744073709551616 : ℚ) : ℝ) ≤ ((801438507 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2538 : ((20827636076231 / 2305843009213693952 : ℚ) : ℝ) ≤ heightZ ((1269 / 32 : ℚ) : ℝ) ∧
    heightZ ((1269 / 32 : ℚ) : ℝ) ≤ ((166621088609851 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((20827636076231 / 2305843009213693952 : ℚ) : ℝ) ≤ Real.exp (-((1269 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-943 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1269 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-943 / 96 : ℚ) : ℝ) ≤ ((166621088609851 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2538 : ((24274401 / 2251799813685248 : ℚ) : ℝ) ≤ logKernel ((1269 / 32 : ℚ) : ℝ) ∧
    logKernel ((1269 / 32 : ℚ) : ℝ) ≤ ((776780837 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2538
  constructor
  · exact (show ((24274401 / 2251799813685248 : ℚ) : ℝ) ≤ zKernel ((20827636076231 / 2305843009213693952 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1269 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((166621088609851 / 18446744073709551616 : ℚ) : ℝ) ≤ ((776780837 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2539 : ((82018934033179 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2539 / 64 : ℚ) : ℝ) ∧
    heightZ ((2539 / 64 : ℚ) : ℝ) ≤ ((164037868066361 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((82018934033179 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2539 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1889 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2539 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1889 / 192 : ℚ) : ℝ) ≤ ((164037868066361 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2539 : ((376440899 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2539 / 64 : ℚ) : ℝ) ∧
    logKernel ((2539 / 64 : ℚ) : ℝ) ≤ ((752881803 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2539
  constructor
  · exact (show ((376440899 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((82018934033179 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2539 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((164037868066361 / 18446744073709551616 : ℚ) : ℝ) ≤ ((752881803 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2540 : ((40373674161323 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((635 / 16 : ℚ) : ℝ) ∧
    heightZ ((635 / 16 : ℚ) : ℝ) ≤ ((161494696645295 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((40373674161323 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((635 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-473 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((635 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-473 / 48 : ℚ) : ℝ) ≤ ((161494696645295 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2540 : ((182429515 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((635 / 16 : ℚ) : ℝ) ∧
    logKernel ((635 / 16 : ℚ) : ℝ) ≤ ((729718065 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2540
  constructor
  · exact (show ((182429515 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((40373674161323 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((635 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((161494696645295 / 18446744073709551616 : ℚ) : ℝ) ≤ ((729718065 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2541 : ((621058411885 / 72057594037927936 : ℚ) : ℝ) ≤ heightZ ((2541 / 64 : ℚ) : ℝ) ∧
    heightZ ((2541 / 64 : ℚ) : ℝ) ≤ ((158990953442563 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((621058411885 / 72057594037927936 : ℚ) : ℝ) ≤ Real.exp (-((2541 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1895 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2541 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1895 / 192 : ℚ) : ℝ) ≤ ((158990953442563 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2541 : ((176816749 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((2541 / 64 : ℚ) : ℝ) ∧
    logKernel ((2541 / 64 : ℚ) : ℝ) ≤ ((707267001 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2541
  constructor
  · exact (show ((176816749 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((621058411885 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2541 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((158990953442563 / 18446744073709551616 : ℚ) : ℝ) ≤ ((707267001 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2542 : ((156526027180293 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1271 / 32 : ℚ) : ℝ) ∧
    heightZ ((1271 / 32 : ℚ) : ℝ) ≤ ((19565753397537 / 2305843009213693952 : ℚ) : ℝ) := by
  have h : ((156526027180293 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1271 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-949 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1271 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-949 / 96 : ℚ) : ℝ) ≤ ((19565753397537 / 2305843009213693952 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2542 : ((342753339 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((1271 / 32 : ℚ) : ℝ) ∧
    logKernel ((1271 / 32 : ℚ) : ℝ) ≤ ((685506683 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2542
  constructor
  · exact (show ((342753339 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((156526027180293 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1271 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((19565753397537 / 2305843009213693952 : ℚ) : ℝ) ≤ ((685506683 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2543 : ((77049658028805 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2543 / 64 : ℚ) : ℝ) ∧
    heightZ ((2543 / 64 : ℚ) : ℝ) ≤ ((154099316057613 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((77049658028805 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2543 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1901 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2543 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1901 / 192 : ℚ) : ℝ) ≤ ((154099316057613 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2543 : ((332207927 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2543 / 64 : ℚ) : ℝ) ∧
    logKernel ((2543 / 64 : ℚ) : ℝ) ≤ ((664415859 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2543
  constructor
  · exact (show ((332207927 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((77049658028805 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2543 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((154099316057613 / 18446744073709551616 : ℚ) : ℝ) ≤ ((664415859 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2544 : ((151710227603687 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((159 / 4 : ℚ) : ℝ) ∧
    heightZ ((159 / 4 : ℚ) : ℝ) ≤ ((75855113801845 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((151710227603687 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((159 / 4 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-119 / 12 : ℚ) : ℝ) ∧
      Real.exp (-((159 / 4 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-119 / 12 : ℚ) : ℝ) ≤ ((75855113801845 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2544 : ((643973927 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((159 / 4 : ℚ) : ℝ) ∧
    logKernel ((159 / 4 : ℚ) : ℝ) ≤ ((160993483 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2544
  constructor
  · exact (show ((643973927 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((151710227603687 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((159 / 4 : ℚ) : ℝ)) hh).trans
      (show zKernel ((75855113801845 / 9223372036854775808 : ℚ) : ℝ) ≤ ((160993483 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2545 : ((74679089266555 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2545 / 64 : ℚ) : ℝ) ∧
    heightZ ((2545 / 64 : ℚ) : ℝ) ≤ ((149358178533113 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((74679089266555 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2545 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1907 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2545 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1907 / 192 : ℚ) : ℝ) ≤ ((149358178533113 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2545 : ((624160933 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2545 / 64 : ℚ) : ℝ) ∧
    logKernel ((2545 / 64 : ℚ) : ℝ) ≤ ((312080469 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2545
  constructor
  · exact (show ((624160933 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((74679089266555 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2545 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((149358178533113 / 18446744073709551616 : ℚ) : ℝ) ≤ ((312080469 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem log_height_bounds_672 : ((132252609588235535 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((1257 / 32 : ℚ) : ℝ) ∧
    Real.log ((1257 / 32 : ℚ) : ℝ) ≤ ((264505219176471073 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((132252609588235535 / 36028797018963968 : ℚ) : ℝ) ≤ ((1257 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1257 / 32 : ℚ) : ℝ) ≤ Real.exp ((264505219176471073 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_672 : heightPower (672 : Fin 988) ≤ ((760782691995655 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_672
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_672 : heightFactor (672 : Fin 988) ≤ ((11558759207 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_672
  obtain ⟨hpl, hph⟩ := kernel_bounds_2513
  obtain ⟨hcl, hch⟩ := kernel_bounds_2514
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2514
  have h : (((1580049 / 512 : ℚ) : ℝ) * (logKernel ((2513 / 64 : ℚ) : ℝ) - logKernel ((1257 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1257 / 32 : ℚ) : ℝ) + Real.log ((1257 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((11558759207 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_673 : ((33066734500607683 / 9007199254740992 : ℚ) : ℝ) ≤ Real.log ((2515 / 64 : ℚ) : ℝ) ∧
    Real.log ((2515 / 64 : ℚ) : ℝ) ≤ ((264533876004861467 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((33066734500607683 / 9007199254740992 : ℚ) : ℝ) ≤ ((2515 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2515 / 64 : ℚ) : ℝ) ≤ Real.exp ((264533876004861467 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_673 : heightPower (673 : Fin 988) ≤ ((380955094403703 / 35184372088832 : ℚ) : ℝ) := by
  have hh := log_height_bounds_673
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_673 : heightFactor (673 : Fin 988) ≤ ((22544182709 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_673
  obtain ⟨hpl, hph⟩ := kernel_bounds_2514
  obtain ⟨hcl, hch⟩ := kernel_bounds_2515
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2515
  have h : (((6325225 / 2048 : ℚ) : ℝ) * (logKernel ((1257 / 32 : ℚ) : ℝ) - logKernel ((2515 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2515 / 64 : ℚ) : ℝ) + Real.log ((2515 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((22544182709 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_674 : ((264562521441151225 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((629 / 16 : ℚ) : ℝ) ∧
    Real.log ((629 / 16 : ℚ) : ℝ) ≤ ((66140630360287807 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((264562521441151225 / 72057594037927936 : ℚ) : ℝ) ≤ ((629 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((629 / 16 : ℚ) : ℝ) ≤ Real.exp ((66140630360287807 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_674 : heightPower (674 : Fin 988) ≤ ((1526075348988117 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_674
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_674 : heightFactor (674 : Fin 988) ≤ ((21985058187 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_674
  obtain ⟨hpl, hph⟩ := kernel_bounds_2515
  obtain ⟨hcl, hch⟩ := kernel_bounds_2516
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2516
  have h : (((395641 / 128 : ℚ) : ℝ) * (logKernel ((2515 / 64 : ℚ) : ℝ) - logKernel ((629 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((629 / 16 : ℚ) : ℝ) + Real.log ((629 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((21985058187 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_675 : ((66147788873598569 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((2517 / 64 : ℚ) : ℝ) ∧
    Real.log ((2517 / 64 : ℚ) : ℝ) ≤ ((264591155494394279 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((66147788873598569 / 18014398509481984 : ℚ) : ℝ) ≤ ((2517 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2517 / 64 : ℚ) : ℝ) ≤ Real.exp ((264591155494394279 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_675 : heightPower (675 : Fin 988) ≤ ((3056660596257819 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_675
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_675 : heightFactor (675 : Fin 988) ≤ ((5359948201 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_675
  obtain ⟨hpl, hph⟩ := kernel_bounds_2516
  obtain ⟨hcl, hch⟩ := kernel_bounds_2517
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2517
  have h : (((6335289 / 2048 : ℚ) : ℝ) * (logKernel ((629 / 16 : ℚ) : ℝ) - logKernel ((2517 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2517 / 64 : ℚ) : ℝ) + Real.log ((2517 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((5359948201 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_676 : ((264619778173633753 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1259 / 32 : ℚ) : ℝ) ∧
    Real.log ((1259 / 32 : ℚ) : ℝ) ≤ ((66154944543408439 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((264619778173633753 / 72057594037927936 : ℚ) : ℝ) ≤ ((1259 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1259 / 32 : ℚ) : ℝ) ≤ Real.exp ((66154944543408439 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_676 : heightPower (676 : Fin 988) ≤ ((1530585225054851 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_676
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_676 : heightFactor (676 : Fin 988) ≤ ((10454021617 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_676
  obtain ⟨hpl, hph⟩ := kernel_bounds_2517
  obtain ⟨hcl, hch⟩ := kernel_bounds_2518
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2518
  have h : (((1585081 / 512 : ℚ) : ℝ) * (logKernel ((2517 / 64 : ℚ) : ℝ) - logKernel ((1259 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1259 / 32 : ℚ) : ℝ) + Real.log ((1259 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((10454021617 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_677 : ((264648389487902021 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2519 / 64 : ℚ) : ℝ) ∧
    Real.log ((2519 / 64 : ℚ) : ℝ) ≤ ((33081048685987753 / 9007199254740992 : ℚ) : ℝ) := by
  have hl : Real.exp ((264648389487902021 / 72057594037927936 : ℚ) : ℝ) ≤ ((2519 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2519 / 64 : ℚ) : ℝ) ≤ Real.exp ((33081048685987753 / 9007199254740992 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_677 : heightPower (677 : Fin 988) ≤ ((3065680259567167 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_677
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_677 : heightFactor (677 : Fin 988) ≤ ((20389474649 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_677
  obtain ⟨hpl, hph⟩ := kernel_bounds_2518
  obtain ⟨hcl, hch⟩ := kernel_bounds_2519
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2519
  have h : (((6345361 / 2048 : ℚ) : ℝ) * (logKernel ((1259 / 32 : ℚ) : ℝ) - logKernel ((2519 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2519 / 64 : ℚ) : ℝ) + Real.log ((2519 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((20389474649 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_678 : ((16542311840388793 / 4503599627370496 : ℚ) : ℝ) ≤ Real.log ((315 / 8 : ℚ) : ℝ) ∧
    Real.log ((315 / 8 : ℚ) : ℝ) ≤ ((264676989446220691 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((16542311840388793 / 4503599627370496 : ℚ) : ℝ) ≤ ((315 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((315 / 8 : ℚ) : ℝ) ≤ Real.exp ((264676989446220691 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_678 : heightPower (678 : Fin 988) ≤ ((3070190024665453 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_678
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_678 : heightFactor (678 : Fin 988) ≤ ((155341879 / 2199023255552 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_678
  obtain ⟨hpl, hph⟩ := kernel_bounds_2519
  obtain ⟨hcl, hch⟩ := kernel_bounds_2520
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2520
  have h : (((99225 / 32 : ℚ) : ℝ) * (logKernel ((2519 / 64 : ℚ) : ℝ) - logKernel ((315 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((315 / 8 : ℚ) : ℝ) + Real.log ((315 / 8 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((155341879 / 2199023255552 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_679 : ((264705578057600625 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2521 / 64 : ℚ) : ℝ) ∧
    Real.log ((2521 / 64 : ℚ) : ℝ) ≤ ((66176394514400157 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((264705578057600625 / 72057594037927936 : ℚ) : ℝ) ≤ ((2521 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2521 / 64 : ℚ) : ℝ) ≤ Real.exp ((66176394514400157 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_679 : heightPower (679 : Fin 988) ≤ ((192168734089985 / 17592186044416 : ℚ) : ℝ) := by
  have hh := log_height_bounds_679
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_679 : heightFactor (679 : Fin 988) ≤ ((19390582369 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_679
  obtain ⟨hpl, hph⟩ := kernel_bounds_2520
  obtain ⟨hcl, hch⟩ := kernel_bounds_2521
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2521
  have h : (((6355441 / 2048 : ℚ) : ℝ) * (logKernel ((315 / 8 : ℚ) : ℝ) - logKernel ((2521 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2521 / 64 : ℚ) : ℝ) + Real.log ((2521 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((19390582369 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_680 : ((132367077665520991 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((1261 / 32 : ℚ) : ℝ) ∧
    Real.log ((1261 / 32 : ℚ) : ℝ) ≤ ((264734155331041985 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((132367077665520991 / 36028797018963968 : ℚ) : ℝ) ≤ ((1261 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1261 / 32 : ℚ) : ℝ) ≤ Real.exp ((264734155331041985 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_680 : heightPower (680 : Fin 988) ≤ ((769802355481311 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_680
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_680 : heightFactor (680 : Fin 988) ≤ ((18909629653 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_680
  obtain ⟨hpl, hph⟩ := kernel_bounds_2521
  obtain ⟨hcl, hch⟩ := kernel_bounds_2522
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2522
  have h : (((1590121 / 512 : ℚ) : ℝ) * (logKernel ((2521 / 64 : ℚ) : ℝ) - logKernel ((1261 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1261 / 32 : ℚ) : ℝ) + Real.log ((1261 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((18909629653 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_681 : ((264762721275534205 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2523 / 64 : ℚ) : ℝ) ∧
    Real.log ((2523 / 64 : ℚ) : ℝ) ≤ ((2068458759965111 / 562949953421312 : ℚ) : ℝ) := by
  have hl : Real.exp ((264762721275534205 / 72057594037927936 : ℚ) : ℝ) ≤ ((2523 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2523 / 64 : ℚ) : ℝ) ≤ Real.exp ((2068458759965111 / 562949953421312 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_681 : heightPower (681 : Fin 988) ≤ ((3083719054157021 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_681
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_681 : heightFactor (681 : Fin 988) ≤ ((18440599483 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_681
  obtain ⟨hpl, hph⟩ := kernel_bounds_2522
  obtain ⟨hcl, hch⟩ := kernel_bounds_2523
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2523
  have h : (((6365529 / 2048 : ℚ) : ℝ) * (logKernel ((1261 / 32 : ℚ) : ℝ) - logKernel ((2523 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2523 / 64 : ℚ) : ℝ) + Real.log ((2523 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((18440599483 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_682 : ((132395637950028027 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((631 / 16 : ℚ) : ℝ) ∧
    Real.log ((631 / 16 : ℚ) : ℝ) ≤ ((264791275900056057 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((132395637950028027 / 36028797018963968 : ℚ) : ℝ) ≤ ((631 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((631 / 16 : ℚ) : ℝ) ≤ Real.exp ((264791275900056057 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_682 : heightPower (682 : Fin 988) ≤ ((3088228642170163 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_682
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_682 : heightFactor (682 : Fin 988) ≤ ((17983196479 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_682
  obtain ⟨hpl, hph⟩ := kernel_bounds_2523
  obtain ⟨hcl, hch⟩ := kernel_bounds_2524
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2524
  have h : (((398161 / 128 : ℚ) : ℝ) * (logKernel ((2523 / 64 : ℚ) : ℝ) - logKernel ((631 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((631 / 16 : ℚ) : ℝ) + Real.log ((631 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((17983196479 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_683 : ((264819819213575617 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2525 / 64 : ℚ) : ℝ) ∧
    Real.log ((2525 / 64 : ℚ) : ℝ) ≤ ((66204954803393905 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((264819819213575617 / 72057594037927936 : ℚ) : ℝ) ≤ ((2525 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2525 / 64 : ℚ) : ℝ) ≤ Real.exp ((66204954803393905 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_683 : heightPower (683 : Fin 988) ≤ ((3092738185999703 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_683
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_683 : heightFactor (683 : Fin 988) ≤ ((17537132575 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_683
  obtain ⟨hpl, hph⟩ := kernel_bounds_2524
  obtain ⟨hcl, hch⟩ := kernel_bounds_2525
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2525
  have h : (((6375625 / 2048 : ℚ) : ℝ) * (logKernel ((631 / 16 : ℚ) : ℝ) - logKernel ((2525 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2525 / 64 : ℚ) : ℝ) + Real.log ((2525 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((17537132575 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_684 : ((66212087806262583 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((1263 / 32 : ℚ) : ℝ) ∧
    Real.log ((1263 / 32 : ℚ) : ℝ) ≤ ((264848351225050335 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((66212087806262583 / 18014398509481984 : ℚ) : ℝ) ≤ ((1263 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1263 / 32 : ℚ) : ℝ) ≤ Real.exp ((264848351225050335 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_684 : heightPower (684 : Fin 988) ≤ ((1548623842840315 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_684
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_684 : heightFactor (684 : Fin 988) ≤ ((8551063419 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_684
  obtain ⟨hpl, hph⟩ := kernel_bounds_2525
  obtain ⟨hcl, hch⟩ := kernel_bounds_2526
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2526
  have h : (((1595169 / 512 : ℚ) : ℝ) * (logKernel ((2525 / 64 : ℚ) : ℝ) - logKernel ((1263 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1263 / 32 : ℚ) : ℝ) + Real.log ((1263 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((8551063419 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_685 : ((132438435971713499 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2527 / 64 : ℚ) : ℝ) ∧
    Real.log ((2527 / 64 : ℚ) : ℝ) ≤ ((264876871943427001 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((132438435971713499 / 36028797018963968 : ℚ) : ℝ) ≤ ((2527 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2527 / 64 : ℚ) : ℝ) ≤ Real.exp ((264876871943427001 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_685 : heightPower (685 : Fin 988) ≤ ((3101757141247893 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_685
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_685 : heightFactor (685 : Fin 988) ≤ ((16677905289 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_685
  obtain ⟨hpl, hph⟩ := kernel_bounds_2526
  obtain ⟨hcl, hch⟩ := kernel_bounds_2527
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2527
  have h : (((6385729 / 2048 : ℚ) : ℝ) * (logKernel ((1263 / 32 : ℚ) : ℝ) - logKernel ((2527 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2527 / 64 : ℚ) : ℝ) + Real.log ((2527 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((16677905289 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_686 : ((264905381377641797 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((79 / 2 : ℚ) : ℝ) ∧
    Real.log ((79 / 2 : ℚ) : ℝ) ≤ ((33113172672205225 / 9007199254740992 : ℚ) : ℝ) := by
  have hl : Real.exp ((264905381377641797 / 72057594037927936 : ℚ) : ℝ) ≤ ((79 / 2 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((79 / 2 : ℚ) : ℝ) ≤ Real.exp ((33113172672205225 / 9007199254740992 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_686 : heightPower (686 : Fin 988) ≤ ((3106266552736399 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_686
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_686 : heightFactor (686 : Fin 988) ≤ ((16264200735 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_686
  obtain ⟨hpl, hph⟩ := kernel_bounds_2527
  obtain ⟨hcl, hch⟩ := kernel_bounds_2528
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2528
  have h : (((6241 / 2 : ℚ) : ℝ) * (logKernel ((2527 / 64 : ℚ) : ℝ) - logKernel ((79 / 2 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((79 / 2 : ℚ) : ℝ) + Real.log ((79 / 2 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((16264200735 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_687 : ((264933879536620305 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2529 / 64 : ℚ) : ℝ) ∧
    Real.log ((2529 / 64 : ℚ) : ℝ) ≤ ((66233469884155077 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((264933879536620305 / 72057594037927936 : ℚ) : ℝ) ≤ ((2529 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2529 / 64 : ℚ) : ℝ) ≤ Real.exp ((66233469884155077 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_687 : heightPower (687 : Fin 988) ≤ ((3110775920181013 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_687
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_687 : heightFactor (687 : Fin 988) ≤ ((7930376299 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_687
  obtain ⟨hpl, hph⟩ := kernel_bounds_2528
  obtain ⟨hcl, hch⟩ := kernel_bounds_2529
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2529
  have h : (((6395841 / 2048 : ℚ) : ℝ) * (logKernel ((79 / 2 : ℚ) : ℝ) - logKernel ((2529 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2529 / 64 : ℚ) : ℝ) + Real.log ((2529 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((7930376299 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_688 : ((264962366429277517 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1265 / 32 : ℚ) : ℝ) ∧
    Real.log ((1265 / 32 : ℚ) : ℝ) ≤ ((16560147901829845 / 4503599627370496 : ℚ) : ℝ) := by
  have hl : Real.exp ((264962366429277517 / 72057594037927936 : ℚ) : ℝ) ≤ ((1265 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1265 / 32 : ℚ) : ℝ) ≤ Real.exp ((16560147901829845 / 4503599627370496 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_688 : heightPower (688 : Fin 988) ≤ ((3115285243616559 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_688
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_688 : heightFactor (688 : Fin 988) ≤ ((60419167 / 1099511627776 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_688
  obtain ⟨hpl, hph⟩ := kernel_bounds_2529
  obtain ⟨hcl, hch⟩ := kernel_bounds_2530
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2530
  have h : (((1600225 / 512 : ℚ) : ℝ) * (logKernel ((2529 / 64 : ℚ) : ℝ) - logKernel ((1265 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1265 / 32 : ℚ) : ℝ) + Real.log ((1265 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((60419167 / 1099511627776 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_689 : ((264990842064517855 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2531 / 64 : ℚ) : ℝ) ∧
    Real.log ((2531 / 64 : ℚ) : ℝ) ≤ ((132495421032258929 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((264990842064517855 / 72057594037927936 : ℚ) : ℝ) ≤ ((2531 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2531 / 64 : ℚ) : ℝ) ≤ Real.exp ((132495421032258929 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_689 : heightPower (689 : Fin 988) ≤ ((779948630769455 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_689
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_689 : heightFactor (689 : Fin 988) ≤ ((15083615365 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_689
  obtain ⟨hpl, hph⟩ := kernel_bounds_2530
  obtain ⟨hcl, hch⟩ := kernel_bounds_2531
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2531
  have h : (((6405961 / 2048 : ℚ) : ℝ) * (logKernel ((1265 / 32 : ℚ) : ℝ) - logKernel ((2531 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2531 / 64 : ℚ) : ℝ) + Real.log ((2531 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((15083615365 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_690 : ((132509653225617595 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((633 / 16 : ℚ) : ℝ) ∧
    Real.log ((633 / 16 : ℚ) : ℝ) ≤ ((265019306451235193 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((132509653225617595 / 36028797018963968 : ℚ) : ℝ) ≤ ((633 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((633 / 16 : ℚ) : ℝ) ≤ Real.exp ((265019306451235193 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_690 : heightPower (690 : Fin 988) ≤ ((3124303758599539 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_690
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_690 : heightFactor (690 : Fin 988) ≤ ((14709436743 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_690
  obtain ⟨hpl, hph⟩ := kernel_bounds_2531
  obtain ⟨hcl, hch⟩ := kernel_bounds_2532
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2532
  have h : (((400689 / 128 : ℚ) : ℝ) * (logKernel ((2531 / 64 : ℚ) : ℝ) - logKernel ((633 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((633 / 16 : ℚ) : ℝ) + Real.log ((633 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((14709436743 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_691 : ((265047759598312859 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2533 / 64 : ℚ) : ℝ) ∧
    Real.log ((2533 / 64 : ℚ) : ℝ) ≤ ((132523879799156431 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((265047759598312859 / 72057594037927936 : ℚ) : ℝ) ≤ ((2533 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2533 / 64 : ℚ) : ℝ) ≤ Real.exp ((132523879799156431 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_691 : heightPower (691 : Fin 988) ≤ ((3128812950216415 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_691
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_691 : heightFactor (691 : Fin 988) ≤ ((14344535173 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_691
  obtain ⟨hpl, hph⟩ := kernel_bounds_2532
  obtain ⟨hcl, hch⟩ := kernel_bounds_2533
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2533
  have h : (((6416089 / 2048 : ℚ) : ℝ) * (logKernel ((633 / 16 : ℚ) : ℝ) - logKernel ((2533 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2533 / 64 : ℚ) : ℝ) + Real.log ((2533 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((14344535173 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_692 : ((66269050378655919 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((1267 / 32 : ℚ) : ℝ) ∧
    Real.log ((1267 / 32 : ℚ) : ℝ) ≤ ((265076201514623679 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((66269050378655919 / 18014398509481984 : ℚ) : ℝ) ≤ ((1267 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1267 / 32 : ℚ) : ℝ) ≤ Real.exp ((265076201514623679 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_692 : heightPower (692 : Fin 988) ≤ ((783330524490777 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_692
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_692 : heightFactor (692 : Fin 988) ≤ ((13988680783 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_692
  obtain ⟨hpl, hph⟩ := kernel_bounds_2533
  obtain ⟨hcl, hch⟩ := kernel_bounds_2534
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2534
  have h : (((1605289 / 512 : ℚ) : ℝ) * (logKernel ((2533 / 64 : ℚ) : ℝ) - logKernel ((1267 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1267 / 32 : ℚ) : ℝ) + Real.log ((1267 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((13988680783 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_693 : ((66276158052257489 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((2535 / 64 : ℚ) : ℝ) ∧
    Real.log ((2535 / 64 : ℚ) : ℝ) ≤ ((265104632209029959 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((66276158052257489 / 18014398509481984 : ℚ) : ℝ) ≤ ((2535 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2535 / 64 : ℚ) : ℝ) ≤ Real.exp ((265104632209029959 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_693 : heightPower (693 : Fin 988) ≤ ((3137831201874237 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_693
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_693 : heightFactor (693 : Fin 988) ≤ ((852603087 / 17592186044416 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_693
  obtain ⟨hpl, hph⟩ := kernel_bounds_2534
  obtain ⟨hcl, hch⟩ := kernel_bounds_2535
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2535
  have h : (((6426225 / 2048 : ℚ) : ℝ) * (logKernel ((1267 / 32 : ℚ) : ℝ) - logKernel ((2535 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2535 / 64 : ℚ) : ℝ) + Real.log ((2535 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((852603087 / 17592186044416 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_694 : ((33141631461297941 / 9007199254740992 : ℚ) : ℝ) ≤ Real.log ((317 / 8 : ℚ) : ℝ) ∧
    Real.log ((317 / 8 : ℚ) : ℝ) ≤ ((265133051690383531 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((33141631461297941 / 9007199254740992 : ℚ) : ℝ) ≤ ((317 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((317 / 8 : ℚ) : ℝ) ≤ Real.exp ((265133051690383531 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_694 : heightPower (694 : Fin 988) ≤ ((1571170130992189 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_694
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_694 : heightFactor (694 : Fin 988) ≤ ((13303222371 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_694
  obtain ⟨hpl, hph⟩ := kernel_bounds_2535
  obtain ⟨hcl, hch⟩ := kernel_bounds_2536
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2536
  have h : (((100489 / 32 : ℚ) : ℝ) * (logKernel ((2535 / 64 : ℚ) : ℝ) - logKernel ((317 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((317 / 8 : ℚ) : ℝ) + Real.log ((317 / 8 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((13303222371 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_695 : ((265161459967525749 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2537 / 64 : ℚ) : ℝ) ∧
    Real.log ((2537 / 64 : ℚ) : ℝ) ≤ ((33145182495940719 / 9007199254740992 : ℚ) : ℝ) := by
  have hl : Real.exp ((265161459967525749 / 72057594037927936 : ℚ) : ℝ) ≤ ((2537 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2537 / 64 : ℚ) : ℝ) ≤ Real.exp ((33145182495940719 / 9007199254740992 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_695 : heightPower (695 : Fin 988) ≤ ((3146849278328069 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_695
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_695 : heightFactor (695 : Fin 988) ≤ ((1621648313 / 35184372088832 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_695
  obtain ⟨hpl, hph⟩ := kernel_bounds_2536
  obtain ⟨hcl, hch⟩ := kernel_bounds_2537
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2537
  have h : (((6436369 / 2048 : ℚ) : ℝ) * (logKernel ((317 / 8 : ℚ) : ℝ) - logKernel ((2537 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2537 / 64 : ℚ) : ℝ) + Real.log ((2537 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1621648313 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_696 : ((132594928524643763 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((1269 / 32 : ℚ) : ℝ) ∧
    Real.log ((1269 / 32 : ℚ) : ℝ) ≤ ((265189857049287529 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((132594928524643763 / 36028797018963968 : ℚ) : ℝ) ≤ ((1269 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1269 / 32 : ℚ) : ℝ) ≤ Real.exp ((265189857049287529 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_696 : heightPower (696 : Fin 988) ≤ ((3151358250939805 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_696
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_696 : heightFactor (696 : Fin 988) ≤ ((6325666929 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_696
  obtain ⟨hpl, hph⟩ := kernel_bounds_2537
  obtain ⟨hcl, hch⟩ := kernel_bounds_2538
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2538
  have h : (((1610361 / 512 : ℚ) : ℝ) * (logKernel ((2537 / 64 : ℚ) : ℝ) - logKernel ((1269 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1269 / 32 : ℚ) : ℝ) + Real.log ((1269 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((6325666929 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_697 : ((16576140184030583 / 4503599627370496 : ℚ) : ℝ) ≤ Real.log ((2539 / 64 : ℚ) : ℝ) ∧
    Real.log ((2539 / 64 : ℚ) : ℝ) ≤ ((265218242944489331 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((16576140184030583 / 4503599627370496 : ℚ) : ℝ) ≤ ((2539 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2539 / 64 : ℚ) : ℝ) ≤ Real.exp ((265218242944489331 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_697 : heightPower (697 : Fin 988) ≤ ((3155867179854041 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_697
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_697 : heightFactor (697 : Fin 988) ≤ ((6168730823 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_697
  obtain ⟨hpl, hph⟩ := kernel_bounds_2538
  obtain ⟨hcl, hch⟩ := kernel_bounds_2539
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2539
  have h : (((6446521 / 2048 : ℚ) : ℝ) * (logKernel ((1269 / 32 : ℚ) : ℝ) - logKernel ((2539 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2539 / 64 : ℚ) : ℝ) + Real.log ((2539 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((6168730823 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_698 : ((66311654415485301 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((635 / 16 : ℚ) : ℝ) ∧
    Real.log ((635 / 16 : ℚ) : ℝ) ≤ ((265246617661941207 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((66311654415485301 / 18014398509481984 : ℚ) : ℝ) ≤ ((635 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((635 / 16 : ℚ) : ℝ) ≤ Real.exp ((265246617661941207 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_698 : heightPower (698 : Fin 988) ≤ ((3160376065105191 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_698
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_698 : heightFactor (698 : Fin 988) ≤ ((12031372107 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_698
  obtain ⟨hpl, hph⟩ := kernel_bounds_2539
  obtain ⟨hcl, hch⟩ := kernel_bounds_2540
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2540
  have h : (((403225 / 128 : ℚ) : ℝ) * (logKernel ((2539 / 64 : ℚ) : ℝ) - logKernel ((635 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((635 / 16 : ℚ) : ℝ) + Real.log ((635 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((12031372107 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_699 : ((265274981210442801 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2541 / 64 : ℚ) : ℝ) ∧
    Real.log ((2541 / 64 : ℚ) : ℝ) ≤ ((66318745302610701 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((265274981210442801 / 72057594037927936 : ℚ) : ℝ) ≤ ((2541 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2541 / 64 : ℚ) : ℝ) ≤ Real.exp ((66318745302610701 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_699 : heightPower (699 : Fin 988) ≤ ((1582442453363815 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_699
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_699 : heightFactor (699 : Fin 988) ≤ ((5866436187 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_699
  obtain ⟨hpl, hph⟩ := kernel_bounds_2540
  obtain ⟨hcl, hch⟩ := kernel_bounds_2541
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2541
  have h : (((6456681 / 2048 : ℚ) : ℝ) * (logKernel ((635 / 16 : ℚ) : ℝ) - logKernel ((2541 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2541 / 64 : ℚ) : ℝ) + Real.log ((2541 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((5866436187 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_700 : ((132651666799391689 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((1271 / 32 : ℚ) : ℝ) ∧
    Real.log ((1271 / 32 : ℚ) : ℝ) ≤ ((265303333598783381 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((132651666799391689 / 36028797018963968 : ℚ) : ℝ) ≤ ((1271 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1271 / 32 : ℚ) : ℝ) ≤ Real.exp ((265303333598783381 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_700 : heightPower (700 : Fin 988) ≤ ((3169393704755689 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_700
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_700 : heightFactor (700 : Fin 988) ≤ ((1430221795 / 35184372088832 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_700
  obtain ⟨hpl, hph⟩ := kernel_bounds_2541
  obtain ⟨hcl, hch⟩ := kernel_bounds_2542
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2542
  have h : (((1615441 / 512 : ℚ) : ℝ) * (logKernel ((2541 / 64 : ℚ) : ℝ) - logKernel ((1271 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1271 / 32 : ℚ) : ℝ) + Real.log ((1271 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1430221795 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_701 : ((132665837417870911 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2543 / 64 : ℚ) : ℝ) ∧
    Real.log ((2543 / 64 : ℚ) : ℝ) ≤ ((265331674835741825 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((132665837417870911 / 36028797018963968 : ℚ) : ℝ) ≤ ((2543 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2543 / 64 : ℚ) : ℝ) ≤ Real.exp ((265331674835741825 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_701 : heightPower (701 : Fin 988) ≤ ((1586951229611831 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_701
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_701 : heightFactor (701 : Fin 988) ≤ ((5578947317 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_701
  obtain ⟨hpl, hph⟩ := kernel_bounds_2542
  obtain ⟨hcl, hch⟩ := kernel_bounds_2543
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2543
  have h : (((6466849 / 2048 : ℚ) : ℝ) * (logKernel ((1271 / 32 : ℚ) : ℝ) - logKernel ((2543 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2543 / 64 : ℚ) : ℝ) + Real.log ((2543 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((5578947317 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_702 : ((265360004930086667 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((159 / 4 : ℚ) : ℝ) ∧
    Real.log ((159 / 4 : ℚ) : ℝ) ≤ ((132680002465043335 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((265360004930086667 / 72057594037927936 : ℚ) : ℝ) ≤ ((159 / 4 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((159 / 4 : ℚ) : ℝ) ≤ Real.exp ((132680002465043335 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_702 : heightPower (702 : Fin 988) ≤ ((3178411170165801 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_702
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_702 : heightFactor (702 : Fin 988) ≤ ((10881054309 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_702
  obtain ⟨hpl, hph⟩ := kernel_bounds_2543
  obtain ⟨hcl, hch⟩ := kernel_bounds_2544
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2544
  have h : (((25281 / 8 : ℚ) : ℝ) * (logKernel ((2543 / 64 : ℚ) : ℝ) - logKernel ((159 / 4 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((159 / 4 : ℚ) : ℝ) + Real.log ((159 / 4 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((10881054309 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_703 : ((265388323890576109 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2545 / 64 : ℚ) : ℝ) ∧
    Real.log ((2545 / 64 : ℚ) : ℝ) ≤ ((16586770243161007 / 4503599627370496 : ℚ) : ℝ) := by
  have hl : Real.exp ((265388323890576109 / 72057594037927936 : ℚ) : ℝ) ≤ ((2545 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2545 / 64 : ℚ) : ℝ) ≤ Real.exp ((16586770243161007 / 4503599627370496 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_703 : heightPower (703 : Fin 988) ≤ ((795729959404079 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_703
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_703 : heightFactor (703 : Fin 988) ≤ ((10611078929 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_703
  obtain ⟨hpl, hph⟩ := kernel_bounds_2544
  obtain ⟨hcl, hch⟩ := kernel_bounds_2545
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2545
  have h : (((6477025 / 2048 : ℚ) : ℝ) * (logKernel ((159 / 4 : ℚ) : ℝ) - logKernel ((2545 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2545 / 64 : ℚ) : ℝ) + Real.log ((2545 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((10611078929 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

end LegendreK6.M2Pilot.Enclosures.Height021
