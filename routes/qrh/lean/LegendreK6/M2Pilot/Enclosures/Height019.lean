import LegendreK6.M2PilotDefinitions
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp

/-! Generated proposals: every bound is checked by Lean, not by trusting Arb. -/
namespace LegendreK6.M2Pilot.Enclosures.Height019
set_option maxRecDepth 100000
set_option maxHeartbeats 0

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

theorem height_z_bounds_2450 : ((658999189108501 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1225 / 32 : ℚ) : ℝ) ∧
    heightZ ((1225 / 32 : ℚ) : ℝ) ≤ ((82374898638563 / 2305843009213693952 : ℚ) : ℝ) := by
  have h : ((658999189108501 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1225 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-811 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1225 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-811 / 96 : ℚ) : ℝ) ≤ ((82374898638563 / 2305843009213693952 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2450 : ((12150896641 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1225 / 32 : ℚ) : ℝ) ∧
    logKernel ((1225 / 32 : ℚ) : ℝ) ≤ ((6075448323 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2450
  constructor
  · exact (show ((12150896641 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((658999189108501 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1225 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((82374898638563 / 2305843009213693952 : ℚ) : ℝ) ≤ ((6075448323 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2451 : ((162195588416693 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((2451 / 64 : ℚ) : ℝ) ∧
    heightZ ((2451 / 64 : ℚ) : ℝ) ≤ ((648782353666775 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((162195588416693 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((2451 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1625 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2451 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1625 / 192 : ℚ) : ℝ) ≤ ((648782353666775 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2451 : ((11777052853 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2451 / 64 : ℚ) : ℝ) ∧
    logKernel ((2451 / 64 : ℚ) : ℝ) ≤ ((5888526429 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2451
  constructor
  · exact (show ((11777052853 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((162195588416693 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2451 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((648782353666775 / 18446744073709551616 : ℚ) : ℝ) ≤ ((5888526429 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2452 : ((79840489447115 / 2305843009213693952 : ℚ) : ℝ) ≤ heightZ ((613 / 16 : ℚ) : ℝ) ∧
    heightZ ((613 / 16 : ℚ) : ℝ) ≤ ((638723915576923 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((79840489447115 / 2305843009213693952 : ℚ) : ℝ) ≤ Real.exp (-((613 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-407 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((613 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-407 / 48 : ℚ) : ℝ) ≤ ((638723915576923 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2452 : ((11414711029 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((613 / 16 : ℚ) : ℝ) ∧
    logKernel ((613 / 16 : ℚ) : ℝ) ≤ ((5707355517 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2452
  constructor
  · exact (show ((11414711029 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((79840489447115 / 2305843009213693952 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((613 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((638723915576923 / 18446744073709551616 : ℚ) : ℝ) ≤ ((5707355517 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2453 : ((628821419115621 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2453 / 64 : ℚ) : ℝ) ∧
    heightZ ((2453 / 64 : ℚ) : ℝ) ≤ ((78602677389453 / 2305843009213693952 : ℚ) : ℝ) := by
  have h : ((628821419115621 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2453 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1631 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2453 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1631 / 192 : ℚ) : ℝ) ≤ ((78602677389453 / 2305843009213693952 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2453 : ((11063517291 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2453 / 64 : ℚ) : ℝ) ∧
    logKernel ((2453 / 64 : ℚ) : ℝ) ≤ ((691469831 / 4503599627370496 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2453
  constructor
  · exact (show ((11063517291 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((628821419115621 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2453 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((78602677389453 / 2305843009213693952 : ℚ) : ℝ) ≤ ((691469831 / 4503599627370496 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2454 : ((309536223316007 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((1227 / 32 : ℚ) : ℝ) ∧
    heightZ ((1227 / 32 : ℚ) : ℝ) ≤ ((619072446632017 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((309536223316007 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((1227 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-817 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1227 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-817 / 96 : ℚ) : ℝ) ≤ ((619072446632017 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2454 : ((10723128649 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1227 / 32 : ℚ) : ℝ) ∧
    logKernel ((1227 / 32 : ℚ) : ℝ) ≤ ((5361564327 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2454
  constructor
  · exact (show ((10723128649 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((309536223316007 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1227 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((619072446632017 / 18446744073709551616 : ℚ) : ℝ) ≤ ((5361564327 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2455 : ((304737308978719 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2455 / 64 : ℚ) : ℝ) ∧
    heightZ ((2455 / 64 : ℚ) : ℝ) ≤ ((609474617957441 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((304737308978719 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2455 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1637 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2455 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1637 / 192 : ℚ) : ℝ) ≤ ((609474617957441 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2455 : ((1299151583 / 9007199254740992 : ℚ) : ℝ) ≤ logKernel ((2455 / 64 : ℚ) : ℝ) ∧
    logKernel ((2455 / 64 : ℚ) : ℝ) ≤ ((10393212669 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2455
  constructor
  · exact (show ((1299151583 / 9007199254740992 : ℚ) : ℝ) ≤ zKernel ((304737308978719 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2455 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((609474617957441 / 18446744073709551616 : ℚ) : ℝ) ≤ ((10393212669 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2456 : ((300012794912165 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((307 / 8 : ℚ) : ℝ) ∧
    heightZ ((307 / 8 : ℚ) : ℝ) ≤ ((600025589824333 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((300012794912165 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((307 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-205 / 24 : ℚ) : ℝ) ∧
      Real.exp (-((307 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-205 / 24 : ℚ) : ℝ) ≤ ((600025589824333 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2456 : ((10073447127 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((307 / 8 : ℚ) : ℝ) ∧
    logKernel ((307 / 8 : ℚ) : ℝ) ≤ ((2518361783 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2456
  constructor
  · exact (show ((10073447127 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((300012794912165 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((307 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((600025589824333 / 18446744073709551616 : ℚ) : ℝ) ≤ ((2518361783 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2457 : ((295361527647061 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2457 / 64 : ℚ) : ℝ) ∧
    heightZ ((2457 / 64 : ℚ) : ℝ) ≤ ((590723055294125 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((295361527647061 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2457 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1643 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2457 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1643 / 192 : ℚ) : ℝ) ≤ ((590723055294125 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2457 : ((9763519741 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2457 / 64 : ℚ) : ℝ) ∧
    logKernel ((2457 / 64 : ℚ) : ℝ) ≤ ((4881759873 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2457
  constructor
  · exact (show ((9763519741 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((295361527647061 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2457 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((590723055294125 / 18446744073709551616 : ℚ) : ℝ) ≤ ((4881759873 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2458 : ((145391185798503 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((1229 / 32 : ℚ) : ℝ) ∧
    heightZ ((1229 / 32 : ℚ) : ℝ) ≤ ((581564743194015 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((145391185798503 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((1229 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-823 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1229 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-823 / 96 : ℚ) : ℝ) ≤ ((581564743194015 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2458 : ((4731563909 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((1229 / 32 : ℚ) : ℝ) ∧
    logKernel ((1229 / 32 : ℚ) : ℝ) ≤ ((9463127823 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2458
  constructor
  · exact (show ((4731563909 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((145391185798503 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1229 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((581564743194015 / 18446744073709551616 : ℚ) : ℝ) ≤ ((9463127823 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2459 : ((286274208781235 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2459 / 64 : ℚ) : ℝ) ∧
    heightZ ((2459 / 64 : ℚ) : ℝ) ≤ ((572548417562473 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((286274208781235 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2459 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1649 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2459 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1649 / 192 : ℚ) : ℝ) ≤ ((572548417562473 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2459 : ((9171977983 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2459 / 64 : ℚ) : ℝ) ∧
    logKernel ((2459 / 64 : ℚ) : ℝ) ≤ ((2292994497 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2459
  constructor
  · exact (show ((9171977983 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((286274208781235 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2459 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((572548417562473 / 18446744073709551616 : ℚ) : ℝ) ≤ ((2292994497 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2460 : ((70458984637917 / 2305843009213693952 : ℚ) : ℝ) ≤ heightZ ((615 / 16 : ℚ) : ℝ) ∧
    heightZ ((615 / 16 : ℚ) : ℝ) ≤ ((563671877103339 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((70458984637917 / 2305843009213693952 : ℚ) : ℝ) ≤ Real.exp (-((615 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-413 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((615 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-413 / 48 : ℚ) : ℝ) ≤ ((563671877103339 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2460 : ((8889785887 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((615 / 16 : ℚ) : ℝ) ∧
    logKernel ((615 / 16 : ℚ) : ℝ) ≤ ((2222446473 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2460
  constructor
  · exact (show ((8889785887 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((70458984637917 / 2305843009213693952 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((615 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((563671877103339 / 18446744073709551616 : ℚ) : ℝ) ≤ ((2222446473 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2461 : ((554932954648385 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2461 / 64 : ℚ) : ℝ) ∧
    heightZ ((2461 / 64 : ℚ) : ℝ) ≤ ((138733238662097 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((554932954648385 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2461 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1655 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2461 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1655 / 192 : ℚ) : ℝ) ≤ ((138733238662097 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2461 : ((8616275929 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2461 / 64 : ℚ) : ℝ) ∧
    logKernel ((2461 / 64 : ℚ) : ℝ) ≤ ((4308137967 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2461
  constructor
  · exact (show ((8616275929 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((554932954648385 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2461 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((138733238662097 / 4611686018427387904 : ℚ) : ℝ) ≤ ((4308137967 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2462 : ((546329516628219 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1231 / 32 : ℚ) : ℝ) ∧
    heightZ ((1231 / 32 : ℚ) : ℝ) ≤ ((273164758314111 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((546329516628219 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1231 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-829 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1231 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-829 / 96 : ℚ) : ℝ) ≤ ((273164758314111 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2462 : ((2087795247 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((1231 / 32 : ℚ) : ℝ) ∧
    logKernel ((1231 / 32 : ℚ) : ℝ) ≤ ((8351180993 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2462
  constructor
  · exact (show ((2087795247 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((546329516628219 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1231 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((273164758314111 / 9223372036854775808 : ℚ) : ℝ) ≤ ((8351180993 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2463 : ((537859462551369 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2463 / 64 : ℚ) : ℝ) ∧
    heightZ ((2463 / 64 : ℚ) : ℝ) ≤ ((134464865637843 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((537859462551369 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2463 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1661 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2463 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1661 / 192 : ℚ) : ℝ) ≤ ((134464865637843 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2463 : ((8094242161 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2463 / 64 : ℚ) : ℝ) ∧
    logKernel ((2463 / 64 : ℚ) : ℝ) ≤ ((4047121083 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2463
  constructor
  · exact (show ((8094242161 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((537859462551369 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2463 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((134464865637843 / 4611686018427387904 : ℚ) : ℝ) ≤ ((4047121083 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2464 : ((264760362245733 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((77 / 2 : ℚ) : ℝ) ∧
    heightZ ((77 / 2 : ℚ) : ℝ) ≤ ((529520724491469 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((264760362245733 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((77 / 2 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-26 / 3 : ℚ) : ℝ) ∧
      Real.exp (-((77 / 2 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-26 / 3 : ℚ) : ℝ) ≤ ((529520724491469 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2464 : ((3922604255 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((77 / 2 : ℚ) : ℝ) ∧
    logKernel ((77 / 2 : ℚ) : ℝ) ≤ ((7845208515 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2464
  constructor
  · exact (show ((3922604255 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((264760362245733 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((77 / 2 : ℚ) : ℝ)) hh).trans
      (show zKernel ((529520724491469 / 18446744073709551616 : ℚ) : ℝ) ≤ ((7845208515 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2465 : ((521311266582371 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2465 / 64 : ℚ) : ℝ) ∧
    heightZ ((2465 / 64 : ℚ) : ℝ) ≤ ((260655633291187 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((521311266582371 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2465 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1667 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2465 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1667 / 192 : ℚ) : ℝ) ≤ ((260655633291187 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2465 : ((7603836819 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2465 / 64 : ℚ) : ℝ) ∧
    logKernel ((2465 / 64 : ℚ) : ℝ) ≤ ((950479603 / 9007199254740992 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2465
  constructor
  · exact (show ((7603836819 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((521311266582371 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2465 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((260655633291187 / 9223372036854775808 : ℚ) : ℝ) ≤ ((950479603 / 9007199254740992 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2466 : ((513229084521121 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1233 / 32 : ℚ) : ℝ) ∧
    heightZ ((1233 / 32 : ℚ) : ℝ) ≤ ((128307271130281 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((513229084521121 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1233 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-835 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1233 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-835 / 96 : ℚ) : ℝ) ≤ ((128307271130281 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2466 : ((7369891355 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1233 / 32 : ℚ) : ℝ) ∧
    logKernel ((1233 / 32 : ℚ) : ℝ) ≤ ((230309105 / 2251799813685248 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2466
  constructor
  · exact (show ((7369891355 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((513229084521121 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1233 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((128307271130281 / 4611686018427387904 : ℚ) : ℝ) ≤ ((230309105 / 2251799813685248 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2467 : ((505272205078591 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2467 / 64 : ℚ) : ℝ) ∧
    heightZ ((2467 / 64 : ℚ) : ℝ) ≤ ((252636102539297 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((505272205078591 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2467 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1673 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2467 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1673 / 192 : ℚ) : ℝ) ≤ ((252636102539297 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2467 : ((7143143635 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2467 / 64 : ℚ) : ℝ) ∧
    logKernel ((2467 / 64 : ℚ) : ℝ) ≤ ((892892955 / 9007199254740992 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2467
  constructor
  · exact (show ((7143143635 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((505272205078591 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2467 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((252636102539297 / 9223372036854775808 : ℚ) : ℝ) ≤ ((892892955 / 9007199254740992 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2468 : ((497438685617739 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((617 / 16 : ℚ) : ℝ) ∧
    heightZ ((617 / 16 : ℚ) : ℝ) ≤ ((248719342808871 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((497438685617739 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((617 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-419 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((617 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-419 / 48 : ℚ) : ℝ) ≤ ((248719342808871 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2468 : ((3461686105 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((617 / 16 : ℚ) : ℝ) ∧
    logKernel ((617 / 16 : ℚ) : ℝ) ≤ ((6923372215 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2468
  constructor
  · exact (show ((3461686105 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((497438685617739 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((617 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((248719342808871 / 9223372036854775808 : ℚ) : ℝ) ≤ ((6923372215 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2469 : ((489726613619317 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2469 / 64 : ℚ) : ℝ) ∧
    heightZ ((2469 / 64 : ℚ) : ℝ) ≤ ((61215826702415 / 2305843009213693952 : ℚ) : ℝ) := by
  have h : ((489726613619317 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2469 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1679 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2469 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1679 / 192 : ℚ) : ℝ) ≤ ((61215826702415 / 2305843009213693952 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2469 : ((838795305 / 9007199254740992 : ℚ) : ℝ) ≤ logKernel ((2469 / 64 : ℚ) : ℝ) ∧
    logKernel ((2469 / 64 : ℚ) : ℝ) ≤ ((6710362445 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2469
  constructor
  · exact (show ((838795305 / 9007199254740992 : ℚ) : ℝ) ≤ zKernel ((489726613619317 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2469 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((61215826702415 / 2305843009213693952 : ℚ) : ℝ) ≤ ((6710362445 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2470 : ((241067053107471 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((1235 / 32 : ℚ) : ℝ) ∧
    heightZ ((1235 / 32 : ℚ) : ℝ) ≤ ((482134106214945 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((241067053107471 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((1235 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-841 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1235 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-841 / 96 : ℚ) : ℝ) ≤ ((482134106214945 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2470 : ((6503906293 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1235 / 32 : ℚ) : ℝ) ∧
    logKernel ((1235 / 32 : ℚ) : ℝ) ≤ ((3251953149 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2470
  constructor
  · exact (show ((6503906293 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((241067053107471 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1235 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((482134106214945 / 18446744073709551616 : ℚ) : ℝ) ≤ ((3251953149 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2471 : ((237329654863699 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2471 / 64 : ℚ) : ℝ) ∧
    heightZ ((2471 / 64 : ℚ) : ℝ) ≤ ((474659309727401 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((237329654863699 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2471 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1685 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2471 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1685 / 192 : ℚ) : ℝ) ≤ ((474659309727401 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2471 : ((6303802133 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2471 / 64 : ℚ) : ℝ) ∧
    logKernel ((2471 / 64 : ℚ) : ℝ) ≤ ((3151901069 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2471
  constructor
  · exact (show ((6303802133 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((237329654863699 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2471 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((474659309727401 / 18446744073709551616 : ℚ) : ℝ) ≤ ((3151901069 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2472 : ((233650199609035 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((309 / 8 : ℚ) : ℝ) ∧
    heightZ ((309 / 8 : ℚ) : ℝ) ≤ ((467300399218073 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((233650199609035 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((309 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-211 / 24 : ℚ) : ℝ) ∧
      Real.exp (-((309 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-211 / 24 : ℚ) : ℝ) ≤ ((467300399218073 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2472 : ((3054927265 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((309 / 8 : ℚ) : ℝ) ∧
    logKernel ((309 / 8 : ℚ) : ℝ) ≤ ((6109854535 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2472
  constructor
  · exact (show ((3054927265 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((233650199609035 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((309 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((467300399218073 / 18446744073709551616 : ℚ) : ℝ) ≤ ((6109854535 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2473 : ((460055578041395 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2473 / 64 : ℚ) : ℝ) ∧
    heightZ ((2473 / 64 : ℚ) : ℝ) ≤ ((230027789020699 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((460055578041395 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2473 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1691 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2473 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1691 / 192 : ℚ) : ℝ) ≤ ((230027789020699 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2473 : ((5921874069 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2473 / 64 : ℚ) : ℝ) ∧
    logKernel ((2473 / 64 : ℚ) : ℝ) ≤ ((2960937037 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2473
  constructor
  · exact (show ((5921874069 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((460055578041395 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2473 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((230027789020699 / 9223372036854775808 : ℚ) : ℝ) ≤ ((2960937037 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2474 : ((452923077406217 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1237 / 32 : ℚ) : ℝ) ∧
    heightZ ((1237 / 32 : ℚ) : ℝ) ≤ ((113230769351555 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((452923077406217 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1237 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-847 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1237 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-847 / 96 : ℚ) : ℝ) ≤ ((113230769351555 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2474 : ((2869838579 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((1237 / 32 : ℚ) : ℝ) ∧
    logKernel ((1237 / 32 : ℚ) : ℝ) ≤ ((5739677163 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2474
  constructor
  · exact (show ((2869838579 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((452923077406217 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1237 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((113230769351555 / 4611686018427387904 : ℚ) : ℝ) ≤ ((5739677163 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2475 : ((445901155943945 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2475 / 64 : ℚ) : ℝ) ∧
    heightZ ((2475 / 64 : ℚ) : ℝ) ≤ ((111475288985987 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((445901155943945 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2475 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1697 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2475 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1697 / 192 : ℚ) : ℝ) ≤ ((111475288985987 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2475 : ((173846433 / 2251799813685248 : ℚ) : ℝ) ≤ logKernel ((2475 / 64 : ℚ) : ℝ) ∧
    logKernel ((2475 / 64 : ℚ) : ℝ) ≤ ((5563085861 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2475
  constructor
  · exact (show ((173846433 / 2251799813685248 : ℚ) : ℝ) ≤ zKernel ((445901155943945 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2475 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((111475288985987 / 4611686018427387904 : ℚ) : ℝ) ≤ ((5563085861 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2476 : ((438988099283407 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((619 / 16 : ℚ) : ℝ) ∧
    heightZ ((619 / 16 : ℚ) : ℝ) ≤ ((219494049641705 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((438988099283407 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((619 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-425 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((619 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-425 / 48 : ℚ) : ℝ) ≤ ((219494049641705 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2476 : ((2695963849 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((619 / 16 : ℚ) : ℝ) ∧
    logKernel ((619 / 16 : ℚ) : ℝ) ≤ ((5391927703 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2476
  constructor
  · exact (show ((2695963849 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((438988099283407 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((619 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((219494049641705 / 9223372036854775808 : ℚ) : ℝ) ≤ ((5391927703 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2477 : ((216091109816145 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2477 / 64 : ℚ) : ℝ) ∧
    heightZ ((2477 / 64 : ℚ) : ℝ) ≤ ((432182219632293 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((216091109816145 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2477 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1703 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2477 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1703 / 192 : ℚ) : ℝ) ≤ ((432182219632293 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2477 : ((5226035523 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2477 / 64 : ℚ) : ℝ) ∧
    logKernel ((2477 / 64 : ℚ) : ℝ) ≤ ((653254441 / 9007199254740992 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2477
  constructor
  · exact (show ((5226035523 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((216091109816145 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2477 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((432182219632293 / 18446744073709551616 : ℚ) : ℝ) ≤ ((653254441 / 9007199254740992 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2478 : ((425481855365079 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1239 / 32 : ℚ) : ℝ) ∧
    heightZ ((1239 / 32 : ℚ) : ℝ) ≤ ((212740927682541 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((425481855365079 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1239 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-853 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1239 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-853 / 96 : ℚ) : ℝ) ≤ ((212740927682541 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2478 : ((5065247313 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1239 / 32 : ℚ) : ℝ) ∧
    logKernel ((1239 / 32 : ℚ) : ℝ) ≤ ((2532623659 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2478
  constructor
  · exact (show ((5065247313 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((425481855365079 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1239 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((212740927682541 / 9223372036854775808 : ℚ) : ℝ) ≤ ((2532623659 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2479 : ((418885370617371 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2479 / 64 : ℚ) : ℝ) ∧
    heightZ ((2479 / 64 : ℚ) : ℝ) ≤ ((209442685308687 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((418885370617371 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2479 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1709 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2479 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1709 / 192 : ℚ) : ℝ) ≤ ((209442685308687 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2479 : ((4909406037 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2479 / 64 : ℚ) : ℝ) ∧
    logKernel ((2479 / 64 : ℚ) : ℝ) ≤ ((2454703021 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2479
  constructor
  · exact (show ((4909406037 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((418885370617371 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2479 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((209442685308687 / 9223372036854775808 : ℚ) : ℝ) ≤ ((2454703021 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2480 : ((412391154886491 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((155 / 4 : ℚ) : ℝ) ∧
    heightZ ((155 / 4 : ℚ) : ℝ) ≤ ((206195577443247 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((412391154886491 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((155 / 4 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-107 / 12 : ℚ) : ℝ) ∧
      Real.exp (-((155 / 4 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-107 / 12 : ℚ) : ℝ) ≤ ((206195577443247 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2480 : ((1189589873 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((155 / 4 : ℚ) : ℝ) ∧
    logKernel ((155 / 4 : ℚ) : ℝ) ≤ ((4758359497 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2480
  constructor
  · exact (show ((1189589873 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((412391154886491 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((155 / 4 : ℚ) : ℝ)) hh).trans
      (show zKernel ((206195577443247 / 9223372036854775808 : ℚ) : ℝ) ≤ ((4758359497 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2481 : ((50749702829787 / 2305843009213693952 : ℚ) : ℝ) ≤ heightZ ((2481 / 64 : ℚ) : ℝ) ∧
    heightZ ((2481 / 64 : ℚ) : ℝ) ≤ ((405997622638299 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((50749702829787 / 2305843009213693952 : ℚ) : ℝ) ≤ Real.exp (-((2481 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1715 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2481 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1715 / 192 : ℚ) : ℝ) ≤ ((405997622638299 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2481 : ((4611960161 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2481 / 64 : ℚ) : ℝ) ∧
    logKernel ((2481 / 64 : ℚ) : ℝ) ≤ ((2305980083 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2481
  constructor
  · exact (show ((4611960161 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((50749702829787 / 2305843009213693952 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2481 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((405997622638299 / 18446744073709551616 : ℚ) : ℝ) ≤ ((2305980083 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem log_height_bounds_608 : ((131323531915031035 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((1225 / 32 : ℚ) : ℝ) ∧
    Real.log ((1225 / 32 : ℚ) : ℝ) ≤ ((262647063830062073 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((131323531915031035 / 36028797018963968 : ℚ) : ℝ) ≤ ((1225 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1225 / 32 : ℚ) : ℝ) ≤ Real.exp ((262647063830062073 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_608 : heightPower (608 : Fin 988) ≤ ((2754397371950053 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_608
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_608 : heightFactor (608 : Fin 988) ≤ ((57623937123 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_608
  obtain ⟨hpl, hph⟩ := kernel_bounds_2449
  obtain ⟨hcl, hch⟩ := kernel_bounds_2450
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2450
  have h : (((1500625 / 512 : ℚ) : ℝ) * (logKernel ((2449 / 64 : ℚ) : ℝ) - logKernel ((1225 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1225 / 32 : ℚ) : ℝ) + Real.log ((1225 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((57623937123 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_609 : ((262676469092268927 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2451 / 64 : ℚ) : ℝ) ∧
    Real.log ((2451 / 64 : ℚ) : ℝ) ≤ ((131338234546134465 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((262676469092268927 / 72057594037927936 : ℚ) : ℝ) ≤ ((2451 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2451 / 64 : ℚ) : ℝ) ≤ Real.exp ((131338234546134465 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_609 : heightPower (609 : Fin 988) ≤ ((2758910282766653 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_609
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_609 : heightFactor (609 : Fin 988) ≤ ((112392338397 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_609
  obtain ⟨hpl, hph⟩ := kernel_bounds_2450
  obtain ⟨hcl, hch⟩ := kernel_bounds_2451
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2451
  have h : (((6007401 / 2048 : ℚ) : ℝ) * (logKernel ((1225 / 32 : ℚ) : ℝ) - logKernel ((2451 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2451 / 64 : ℚ) : ℝ) + Real.log ((2451 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((112392338397 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_610 : ((262705862359671369 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((613 / 16 : ℚ) : ℝ) ∧
    Real.log ((613 / 16 : ℚ) : ℝ) ≤ ((65676465589917843 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((262705862359671369 / 72057594037927936 : ℚ) : ℝ) ≤ ((613 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((613 / 16 : ℚ) : ℝ) ≤ Real.exp ((65676465589917843 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_610 : heightPower (610 : Fin 988) ≤ ((690855786682137 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_610
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_610 : heightFactor (610 : Fin 988) ≤ ((13700939075 / 35184372088832 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_610
  obtain ⟨hpl, hph⟩ := kernel_bounds_2451
  obtain ⟨hcl, hch⟩ := kernel_bounds_2452
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2452
  have h : (((375769 / 128 : ℚ) : ℝ) * (logKernel ((2451 / 64 : ℚ) : ℝ) - logKernel ((613 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((613 / 16 : ℚ) : ℝ) + Real.log ((613 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((13700939075 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_611 : ((262735243642051093 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2453 / 64 : ℚ) : ℝ) ∧
    Real.log ((2453 / 64 : ℚ) : ℝ) ≤ ((32841905455256387 / 9007199254740992 : ℚ) : ℝ) := by
  have hl : Real.exp ((262735243642051093 / 72057594037927936 : ℚ) : ℝ) ≤ ((2453 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2453 / 64 : ℚ) : ℝ) ≤ Real.exp ((32841905455256387 / 9007199254740992 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_611 : heightPower (611 : Fin 988) ≤ ((691983990968487 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_611
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_611 : heightFactor (611 : Fin 988) ≤ ((6680727937 / 17592186044416 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_611
  obtain ⟨hpl, hph⟩ := kernel_bounds_2452
  obtain ⟨hcl, hch⟩ := kernel_bounds_2453
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2453
  have h : (((6017209 / 2048 : ℚ) : ℝ) * (logKernel ((613 / 16 : ℚ) : ℝ) - logKernel ((2453 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2453 / 64 : ℚ) : ℝ) + Real.log ((2453 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((6680727937 / 17592186044416 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_612 : ((131382306474588917 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((1227 / 32 : ℚ) : ℝ) ∧
    Real.log ((1227 / 32 : ℚ) : ℝ) ≤ ((262764612949177837 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((131382306474588917 / 36028797018963968 : ℚ) : ℝ) ≤ ((1227 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1227 / 32 : ℚ) : ℝ) ≤ Real.exp ((262764612949177837 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_612 : heightPower (612 : Fin 988) ≤ ((2772448734241015 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_612
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_612 : heightFactor (612 : Fin 988) ≤ ((52121517491 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_612
  obtain ⟨hpl, hph⟩ := kernel_bounds_2453
  obtain ⟨hcl, hch⟩ := kernel_bounds_2454
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2454
  have h : (((1505529 / 512 : ℚ) : ℝ) * (logKernel ((2453 / 64 : ℚ) : ℝ) - logKernel ((1227 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1227 / 32 : ℚ) : ℝ) + Real.log ((1227 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((52121517491 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_613 : ((262793970290809387 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2455 / 64 : ℚ) : ℝ) ∧
    Real.log ((2455 / 64 : ℚ) : ℝ) ≤ ((131396985145404695 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((262793970290809387 / 72057594037927936 : ℚ) : ℝ) ≤ ((2455 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2455 / 64 : ℚ) : ℝ) ≤ Real.exp ((131396985145404695 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_613 : heightPower (613 : Fin 988) ≤ ((694240364466967 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_613
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_613 : heightFactor (613 : Fin 988) ≤ ((101660012191 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_613
  obtain ⟨hpl, hph⟩ := kernel_bounds_2454
  obtain ⟨hcl, hch⟩ := kernel_bounds_2455
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2455
  have h : (((6027025 / 2048 : ℚ) : ℝ) * (logKernel ((1227 / 32 : ℚ) : ℝ) - logKernel ((2455 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2455 / 64 : ℚ) : ℝ) + Real.log ((2455 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((101660012191 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_614 : ((32852914459586453 / 9007199254740992 : ℚ) : ℝ) ≤ Real.log ((307 / 8 : ℚ) : ℝ) ∧
    Real.log ((307 / 8 : ℚ) : ℝ) ≤ ((262823315676691627 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((32852914459586453 / 9007199254740992 : ℚ) : ℝ) ≤ ((307 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((307 / 8 : ℚ) : ℝ) ≤ Real.exp ((262823315676691627 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_614 : heightPower (614 : Fin 988) ≤ ((1390737067396287 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_614
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_614 : heightFactor (614 : Fin 988) ≤ ((49570477699 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_614
  obtain ⟨hpl, hph⟩ := kernel_bounds_2455
  obtain ⟨hcl, hch⟩ := kernel_bounds_2456
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2456
  have h : (((94249 / 32 : ℚ) : ℝ) * (logKernel ((2455 / 64 : ℚ) : ℝ) - logKernel ((307 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((307 / 8 : ℚ) : ℝ) + Real.log ((307 / 8 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((49570477699 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_615 : ((131426324558279259 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2457 / 64 : ℚ) : ℝ) ∧
    Real.log ((2457 / 64 : ℚ) : ℝ) ≤ ((262852649116558521 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((131426324558279259 / 36028797018963968 : ℚ) : ℝ) ≤ ((2457 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2457 / 64 : ℚ) : ℝ) ≤ Real.exp ((262852649116558521 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_615 : heightPower (615 : Fin 988) ≤ ((1392993382526579 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_615
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_615 : heightFactor (615 : Fin 988) ≤ ((24171070383 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_615
  obtain ⟨hpl, hph⟩ := kernel_bounds_2456
  obtain ⟨hcl, hch⟩ := kernel_bounds_2457
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2457
  have h : (((6036849 / 2048 : ℚ) : ℝ) * (logKernel ((307 / 8 : ℚ) : ℝ) - logKernel ((2457 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2457 / 64 : ℚ) : ℝ) + Real.log ((2457 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((24171070383 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_616 : ((65720492655033039 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((1229 / 32 : ℚ) : ℝ) ∧
    Real.log ((1229 / 32 : ℚ) : ℝ) ≤ ((262881970620132159 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((65720492655033039 / 18014398509481984 : ℚ) : ℝ) ≤ ((1229 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1229 / 32 : ℚ) : ℝ) ≤ Real.exp ((262881970620132159 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_616 : heightPower (616 : Fin 988) ≤ ((2790499348687597 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_616
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_616 : heightFactor (616 : Fin 988) ≤ ((94288446675 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_616
  obtain ⟨hpl, hph⟩ := kernel_bounds_2457
  obtain ⟨hcl, hch⟩ := kernel_bounds_2458
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2458
  have h : (((1510441 / 512 : ℚ) : ℝ) * (logKernel ((2457 / 64 : ℚ) : ℝ) - logKernel ((1229 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1229 / 32 : ℚ) : ℝ) + Real.log ((1229 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((94288446675 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_617 : ((131455640098561381 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2459 / 64 : ℚ) : ℝ) ∧
    Real.log ((2459 / 64 : ℚ) : ℝ) ≤ ((262911280197122765 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((131455640098561381 / 36028797018963968 : ℚ) : ℝ) ≤ ((2459 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2459 / 64 : ℚ) : ℝ) ≤ Real.exp ((262911280197122765 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_617 : heightPower (617 : Fin 988) ≤ ((698752971433455 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_617
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_617 : heightFactor (617 : Fin 988) ≤ ((91951945093 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_617
  obtain ⟨hpl, hph⟩ := kernel_bounds_2458
  obtain ⟨hcl, hch⟩ := kernel_bounds_2459
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2459
  have h : (((6046681 / 2048 : ℚ) : ℝ) * (logKernel ((1229 / 32 : ℚ) : ℝ) - logKernel ((2459 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2459 / 64 : ℚ) : ℝ) + Real.log ((2459 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((91951945093 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_618 : ((262940577857228717 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((615 / 16 : ℚ) : ℝ) ∧
    Real.log ((615 / 16 : ℚ) : ℝ) ≤ ((16433786116076795 / 4503599627370496 : ℚ) : ℝ) := by
  have hl : Real.exp ((262940577857228717 / 72057594037927936 : ℚ) : ℝ) ≤ ((615 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((615 / 16 : ℚ) : ℝ) ≤ Real.exp ((16433786116076795 / 4503599627370496 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_618 : heightPower (618 : Fin 988) ≤ ((2799524376229713 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_618
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_618 : heightFactor (618 : Fin 988) ≤ ((11209163537 / 35184372088832 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_618
  obtain ⟨hpl, hph⟩ := kernel_bounds_2459
  obtain ⟨hcl, hch⟩ := kernel_bounds_2460
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2460
  have h : (((378225 / 128 : ℚ) : ℝ) * (logKernel ((2459 / 64 : ℚ) : ℝ) - logKernel ((615 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((615 / 16 : ℚ) : ℝ) + Real.log ((615 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((11209163537 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_619 : ((131484931805068289 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2461 / 64 : ℚ) : ℝ) ∧
    Real.log ((2461 / 64 : ℚ) : ℝ) ≤ ((262969863610136581 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((131484931805068289 / 36028797018963968 : ℚ) : ℝ) ≤ ((2461 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2461 / 64 : ℚ) : ℝ) ≤ Real.exp ((262969863610136581 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_619 : heightPower (619 : Fin 988) ≤ ((1402018410106557 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_619
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_619 : heightFactor (619 : Fin 988) ≤ ((87451104115 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_619
  obtain ⟨hpl, hph⟩ := kernel_bounds_2460
  obtain ⟨hcl, hch⟩ := kernel_bounds_2461
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2461
  have h : (((6056521 / 2048 : ℚ) : ℝ) * (logKernel ((615 / 16 : ℚ) : ℝ) - logKernel ((2461 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2461 / 64 : ℚ) : ℝ) + Real.log ((2461 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((87451104115 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_620 : ((131499568732760547 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((1231 / 32 : ℚ) : ℝ) ∧
    Real.log ((1231 / 32 : ℚ) : ℝ) ≤ ((262999137465521097 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((131499568732760547 / 36028797018963968 : ℚ) : ℝ) ≤ ((1231 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1231 / 32 : ℚ) : ℝ) ≤ Real.exp ((262999137465521097 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_620 : heightPower (620 : Fin 988) ≤ ((2808549217721813 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_620
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_620 : heightFactor (620 : Fin 988) ≤ ((42641967903 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_620
  obtain ⟨hpl, hph⟩ := kernel_bounds_2461
  obtain ⟨hcl, hch⟩ := kernel_bounds_2462
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2462
  have h : (((1515361 / 512 : ℚ) : ℝ) * (logKernel ((2461 / 64 : ℚ) : ℝ) - logKernel ((1231 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1231 / 32 : ℚ) : ℝ) + Real.log ((1231 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((42641967903 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_621 : ((65757099858261307 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((2463 / 64 : ℚ) : ℝ) ∧
    Real.log ((2463 / 64 : ℚ) : ℝ) ≤ ((263028399433045231 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((65757099858261307 / 18014398509481984 : ℚ) : ℝ) ≤ ((2463 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2463 / 64 : ℚ) : ℝ) ≤ Real.exp ((263028399433045231 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_621 : heightPower (621 : Fin 988) ≤ ((1406530784396779 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_621
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_621 : heightFactor (621 : Fin 988) ≤ ((20792610293 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_621
  obtain ⟨hpl, hph⟩ := kernel_bounds_2462
  obtain ⟨hcl, hch⟩ := kernel_bounds_2463
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2463
  have h : (((6066369 / 2048 : ℚ) : ℝ) * (logKernel ((1231 / 32 : ℚ) : ℝ) - logKernel ((2463 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2463 / 64 : ℚ) : ℝ) + Real.log ((2463 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((20792610293 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_622 : ((263057649522360177 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((77 / 2 : ℚ) : ℝ) ∧
    Real.log ((77 / 2 : ℚ) : ℝ) ≤ ((65764412380590045 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((263057649522360177 / 72057594037927936 : ℚ) : ℝ) ≤ ((77 / 2 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((77 / 2 : ℚ) : ℝ) ≤ Real.exp ((65764412380590045 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_622 : heightPower (622 : Fin 988) ≤ ((2817573873466049 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_622
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_622 : heightFactor (622 : Fin 988) ≤ ((81109291711 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_622
  obtain ⟨hpl, hph⟩ := kernel_bounds_2463
  obtain ⟨hcl, hch⟩ := kernel_bounds_2464
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2464
  have h : (((5929 / 2 : ℚ) : ℝ) * (logKernel ((2463 / 64 : ℚ) : ℝ) - logKernel ((77 / 2 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((77 / 2 : ℚ) : ℝ) + Real.log ((77 / 2 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((81109291711 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_623 : ((263086887743105389 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2465 / 64 : ℚ) : ℝ) ∧
    Real.log ((2465 / 64 : ℚ) : ℝ) ≤ ((16442930483944087 / 4503599627370496 : ℚ) : ℝ) := by
  have hl : Real.exp ((263086887743105389 / 72057594037927936 : ℚ) : ℝ) ≤ ((2465 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2465 / 64 : ℚ) : ℝ) ≤ Real.exp ((16442930483944087 / 4503599627370496 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_623 : heightPower (623 : Fin 988) ≤ ((2822086131776939 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_623
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_623 : heightFactor (623 : Fin 988) ≤ ((39549595891 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_623
  obtain ⟨hpl, hph⟩ := kernel_bounds_2464
  obtain ⟨hcl, hch⟩ := kernel_bounds_2465
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2465
  have h : (((6076225 / 2048 : ℚ) : ℝ) * (logKernel ((77 / 2 : ℚ) : ℝ) - logKernel ((2465 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2465 / 64 : ℚ) : ℝ) + Real.log ((2465 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((39549595891 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_624 : ((131558057052454291 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((1233 / 32 : ℚ) : ℝ) ∧
    Real.log ((1233 / 32 : ℚ) : ℝ) ≤ ((263116114104908585 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((131558057052454291 / 36028797018963968 : ℚ) : ℝ) ≤ ((1233 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1233 / 32 : ℚ) : ℝ) ≤ Real.exp ((263116114104908585 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_624 : heightPower (624 : Fin 988) ≤ ((2826598343763837 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_624
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_624 : heightFactor (624 : Fin 988) ≤ ((38569438897 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_624
  obtain ⟨hpl, hph⟩ := kernel_bounds_2465
  obtain ⟨hcl, hch⟩ := kernel_bounds_2466
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2466
  have h : (((1520289 / 512 : ℚ) : ℝ) * (logKernel ((2465 / 64 : ℚ) : ℝ) - logKernel ((1233 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1233 / 32 : ℚ) : ℝ) + Real.log ((1233 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((38569438897 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_625 : ((65786332154346441 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((2467 / 64 : ℚ) : ℝ) ∧
    Real.log ((2467 / 64 : ℚ) : ℝ) ≤ ((263145328617385767 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((65786332154346441 / 18014398509481984 : ℚ) : ℝ) ≤ ((2467 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2467 / 64 : ℚ) : ℝ) ≤ Real.exp ((263145328617385767 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_625 : heightPower (625 : Fin 988) ≤ ((2831110509464305 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_625
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_625 : heightFactor (625 : Fin 988) ≤ ((75227117411 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_625
  obtain ⟨hpl, hph⟩ := kernel_bounds_2466
  obtain ⟨hcl, hch⟩ := kernel_bounds_2467
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2467
  have h : (((6086089 / 2048 : ℚ) : ℝ) * (logKernel ((1233 / 32 : ℚ) : ℝ) - logKernel ((2467 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2467 / 64 : ℚ) : ℝ) + Real.log ((2467 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((75227117411 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_626 : ((131587265645070627 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((617 / 16 : ℚ) : ℝ) ∧
    Real.log ((617 / 16 : ℚ) : ℝ) ≤ ((263174531290141257 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((131587265645070627 / 36028797018963968 : ℚ) : ℝ) ≤ ((617 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((617 / 16 : ℚ) : ℝ) ≤ Real.exp ((263174531290141257 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_626 : heightPower (626 : Fin 988) ≤ ((708905657228965 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_626
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_626 : heightFactor (626 : Fin 988) ≤ ((73362708783 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_626
  obtain ⟨hpl, hph⟩ := kernel_bounds_2467
  obtain ⟨hcl, hch⟩ := kernel_bounds_2468
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2468
  have h : (((380689 / 128 : ℚ) : ℝ) * (logKernel ((2467 / 64 : ℚ) : ℝ) - logKernel ((617 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((617 / 16 : ℚ) : ℝ) + Real.log ((617 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((73362708783 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_627 : ((263203722132767697 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2469 / 64 : ℚ) : ℝ) ∧
    Real.log ((2469 / 64 : ℚ) : ℝ) ≤ ((65800930533191925 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((263203722132767697 / 72057594037927936 : ℚ) : ℝ) ≤ ((2469 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2469 / 64 : ℚ) : ℝ) ≤ Real.exp ((65800930533191925 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_627 : heightPower (627 : Fin 988) ≤ ((2840134702155973 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_627
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_627 : heightFactor (627 : Fin 988) ≤ ((71544479789 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_627
  obtain ⟨hpl, hph⟩ := kernel_bounds_2468
  obtain ⟨hcl, hch⟩ := kernel_bounds_2469
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2469
  have h : (((6095961 / 2048 : ℚ) : ℝ) * (logKernel ((617 / 16 : ℚ) : ℝ) - logKernel ((2469 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2469 / 64 : ℚ) : ℝ) + Real.log ((2469 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((71544479789 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_628 : ((263232901154846083 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1235 / 32 : ℚ) : ℝ) ∧
    Real.log ((1235 / 32 : ℚ) : ℝ) ≤ ((131616450577423043 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((263232901154846083 / 72057594037927936 : ℚ) : ℝ) ≤ ((1235 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1235 / 32 : ℚ) : ℝ) ≤ Real.exp ((131616450577423043 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_628 : heightPower (628 : Fin 988) ≤ ((2844646729222071 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_628
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_628 : heightFactor (628 : Fin 988) ≤ ((34885643653 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_628
  obtain ⟨hpl, hph⟩ := kernel_bounds_2469
  obtain ⟨hcl, hch⟩ := kernel_bounds_2470
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2470
  have h : (((1525225 / 512 : ℚ) : ℝ) * (logKernel ((2469 / 64 : ℚ) : ℝ) - logKernel ((1235 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1235 / 32 : ℚ) : ℝ) + Real.log ((1235 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((34885643653 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_629 : ((131631034182972885 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2471 / 64 : ℚ) : ℝ) ∧
    Real.log ((2471 / 64 : ℚ) : ℝ) ≤ ((263262068365945773 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((131631034182972885 / 36028797018963968 : ℚ) : ℝ) ≤ ((2471 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2471 / 64 : ℚ) : ℝ) ≤ Real.exp ((263262068365945773 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_629 : heightPower (629 : Fin 988) ≤ ((2849158710151533 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_629
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_629 : heightFactor (629 : Fin 988) ≤ ((8505252061 / 35184372088832 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_629
  obtain ⟨hpl, hph⟩ := kernel_bounds_2470
  obtain ⟨hcl, hch⟩ := kernel_bounds_2471
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2471
  have h : (((6105841 / 2048 : ℚ) : ℝ) * (logKernel ((1235 / 32 : ℚ) : ℝ) - logKernel ((2471 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2471 / 64 : ℚ) : ℝ) + Real.log ((2471 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((8505252061 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_630 : ((263291223775624501 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((309 / 8 : ℚ) : ℝ) ∧
    Real.log ((309 / 8 : ℚ) : ℝ) ≤ ((32911402971953063 / 9007199254740992 : ℚ) : ℝ) := by
  have hl : Real.exp ((263291223775624501 / 72057594037927936 : ℚ) : ℝ) ≤ ((309 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((309 / 8 : ℚ) : ℝ) ≤ Real.exp ((32911402971953063 / 9007199254740992 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_630 : heightPower (630 : Fin 988) ≤ ((2853670644981695 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_630
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_630 : heightFactor (630 : Fin 988) ≤ ((16588895017 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_630
  obtain ⟨hpl, hph⟩ := kernel_bounds_2471
  obtain ⟨hcl, hch⟩ := kernel_bounds_2472
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2472
  have h : (((95481 / 32 : ℚ) : ℝ) * (logKernel ((2471 / 64 : ℚ) : ℝ) - logKernel ((309 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((309 / 8 : ℚ) : ℝ) + Real.log ((309 / 8 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((16588895017 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_631 : ((131660183696714209 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2473 / 64 : ℚ) : ℝ) ∧
    Real.log ((2473 / 64 : ℚ) : ℝ) ≤ ((263320367393428421 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((131660183696714209 / 36028797018963968 : ℚ) : ℝ) ≤ ((2473 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2473 / 64 : ℚ) : ℝ) ≤ Real.exp ((263320367393428421 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_631 : heightPower (631 : Fin 988) ≤ ((2858182533749845 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_631
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_631 : heightFactor (631 : Fin 988) ≤ ((64710917679 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_631
  obtain ⟨hpl, hph⟩ := kernel_bounds_2472
  obtain ⟨hcl, hch⟩ := kernel_bounds_2473
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2473
  have h : (((6115729 / 2048 : ℚ) : ℝ) * (logKernel ((309 / 8 : ℚ) : ℝ) - logKernel ((2473 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2473 / 64 : ℚ) : ℝ) + Real.log ((2473 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((64710917679 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_632 : ((131674749614446045 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((1237 / 32 : ℚ) : ℝ) ∧
    Real.log ((1237 / 32 : ℚ) : ℝ) ≤ ((263349499228892093 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((131674749614446045 / 36028797018963968 : ℚ) : ℝ) ≤ ((1237 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1237 / 32 : ℚ) : ℝ) ≤ Real.exp ((263349499228892093 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_632 : heightPower (632 : Fin 988) ≤ ((2862694376493229 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_632
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_632 : heightFactor (632 : Fin 988) ≤ ((63106995185 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_632
  obtain ⟨hpl, hph⟩ := kernel_bounds_2473
  obtain ⟨hcl, hch⟩ := kernel_bounds_2474
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2474
  have h : (((1530169 / 512 : ℚ) : ℝ) * (logKernel ((2473 / 64 : ℚ) : ℝ) - logKernel ((1237 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1237 / 32 : ℚ) : ℝ) + Real.log ((1237 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((63106995185 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_633 : ((65844654822884631 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((2475 / 64 : ℚ) : ℝ) ∧
    Real.log ((2475 / 64 : ℚ) : ℝ) ≤ ((263378619291538527 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((65844654822884631 / 18014398509481984 : ℚ) : ℝ) ≤ ((2475 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2475 / 64 : ℚ) : ℝ) ≤ Real.exp ((263378619291538527 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_633 : heightPower (633 : Fin 988) ≤ ((1433603086624523 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_633
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_633 : heightFactor (633 : Fin 988) ≤ ((15385701009 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_633
  obtain ⟨hpl, hph⟩ := kernel_bounds_2474
  obtain ⟨hcl, hch⟩ := kernel_bounds_2475
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2475
  have h : (((6125625 / 2048 : ℚ) : ℝ) * (logKernel ((1237 / 32 : ℚ) : ℝ) - logKernel ((2475 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2475 / 64 : ℚ) : ℝ) + Real.log ((2475 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((15385701009 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_634 : ((263407727590879185 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((619 / 16 : ℚ) : ℝ) ∧
    Real.log ((619 / 16 : ℚ) : ℝ) ≤ ((65851931897719797 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((263407727590879185 / 72057594037927936 : ℚ) : ℝ) ≤ ((619 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((619 / 16 : ℚ) : ℝ) ≤ Real.exp ((65851931897719797 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_634 : heightPower (634 : Fin 988) ≤ ((2871717924054449 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_634
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_634 : heightFactor (634 : Fin 988) ≤ ((7502170079 / 35184372088832 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_634
  obtain ⟨hpl, hph⟩ := kernel_bounds_2475
  obtain ⟨hcl, hch⟩ := kernel_bounds_2476
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2476
  have h : (((383161 / 128 : ℚ) : ℝ) * (logKernel ((2475 / 64 : ℚ) : ℝ) - logKernel ((619 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((619 / 16 : ℚ) : ℝ) + Real.log ((619 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((7502170079 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_635 : ((263436824136414019 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2477 / 64 : ℚ) : ℝ) ∧
    Real.log ((2477 / 64 : ℚ) : ℝ) ≤ ((131718412068207011 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((263436824136414019 / 72057594037927936 : ℚ) : ℝ) ≤ ((2477 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2477 / 64 : ℚ) : ℝ) ≤ Real.exp ((131718412068207011 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_635 : heightPower (635 : Fin 988) ≤ ((2876229628946549 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_635
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_635 : heightFactor (635 : Fin 988) ≤ ((58529705709 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_635
  obtain ⟨hpl, hph⟩ := kernel_bounds_2476
  obtain ⟨hcl, hch⟩ := kernel_bounds_2477
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2477
  have h : (((6135529 / 2048 : ℚ) : ℝ) * (logKernel ((619 / 16 : ℚ) : ℝ) - logKernel ((2477 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2477 / 64 : ℚ) : ℝ) + Real.log ((2477 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((58529705709 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_636 : ((263465908937631467 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1239 / 32 : ℚ) : ℝ) ∧
    Real.log ((1239 / 32 : ℚ) : ℝ) ≤ ((131732954468815735 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((263465908937631467 / 72057594037927936 : ℚ) : ℝ) ≤ ((1239 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1239 / 32 : ℚ) : ℝ) ≤ Real.exp ((131732954468815735 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_636 : heightPower (636 : Fin 988) ≤ ((360092660995301 / 35184372088832 : ℚ) : ℝ) := by
  have hh := log_height_bounds_636
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_636 : heightFactor (636 : Fin 988) ≤ ((57078903737 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_636
  obtain ⟨hpl, hph⟩ := kernel_bounds_2477
  obtain ⟨hcl, hch⟩ := kernel_bounds_2478
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2478
  have h : (((1535121 / 512 : ℚ) : ℝ) * (logKernel ((2477 / 64 : ℚ) : ℝ) - logKernel ((1239 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1239 / 32 : ℚ) : ℝ) + Real.log ((1239 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((57078903737 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_637 : ((65873745501002121 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((2479 / 64 : ℚ) : ℝ) ∧
    Real.log ((2479 / 64 : ℚ) : ℝ) ≤ ((263494982004008487 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((65873745501002121 / 18014398509481984 : ℚ) : ℝ) ≤ ((2479 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2479 / 64 : ℚ) : ℝ) ≤ Real.exp ((263494982004008487 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_637 : heightPower (637 : Fin 988) ≤ ((360656612642381 / 35184372088832 : ℚ) : ℝ) := by
  have hh := log_height_bounds_637
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_637 : heightFactor (637 : Fin 988) ≤ ((55664042329 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_637
  obtain ⟨hpl, hph⟩ := kernel_bounds_2478
  obtain ⟨hcl, hch⟩ := kernel_bounds_2479
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2479
  have h : (((6145441 / 2048 : ℚ) : ℝ) * (logKernel ((1239 / 32 : ℚ) : ℝ) - logKernel ((2479 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2479 / 64 : ℚ) : ℝ) + Real.log ((2479 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((55664042329 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_638 : ((2058781588632895 / 562949953421312 : ℚ) : ℝ) ≤ Real.log ((155 / 4 : ℚ) : ℝ) ∧
    Real.log ((155 / 4 : ℚ) : ℝ) ≤ ((263524043345010563 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((2058781588632895 / 562949953421312 : ℚ) : ℝ) ≤ ((155 / 4 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((155 / 4 : ℚ) : ℝ) ≤ Real.exp ((263524043345010563 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_638 : heightPower (638 : Fin 988) ≤ ((2889764468513441 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_638
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_638 : heightFactor (638 : Fin 988) ≤ ((13571057919 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_638
  obtain ⟨hpl, hph⟩ := kernel_bounds_2479
  obtain ⟨hcl, hch⟩ := kernel_bounds_2480
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2480
  have h : (((24025 / 8 : ℚ) : ℝ) * (logKernel ((2479 / 64 : ℚ) : ℝ) - logKernel ((155 / 4 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((155 / 4 : ℚ) : ℝ) + Real.log ((155 / 4 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((13571057919 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_639 : ((131776546485045869 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2481 / 64 : ℚ) : ℝ) ∧
    Real.log ((2481 / 64 : ℚ) : ℝ) ≤ ((263553092970091741 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((131776546485045869 / 36028797018963968 : ℚ) : ℝ) ≤ ((2481 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2481 / 64 : ℚ) : ℝ) ≤ Real.exp ((263553092970091741 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_639 : heightPower (639 : Fin 988) ≤ ((1447137995061259 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_639
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_639 : heightFactor (639 : Fin 988) ≤ ((52938603983 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_639
  obtain ⟨hpl, hph⟩ := kernel_bounds_2480
  obtain ⟨hcl, hch⟩ := kernel_bounds_2481
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2481
  have h : (((6155361 / 2048 : ℚ) : ℝ) * (logKernel ((155 / 4 : ℚ) : ℝ) - logKernel ((2481 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2481 / 64 : ℚ) : ℝ) + Real.log ((2481 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((52938603983 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

end LegendreK6.M2Pilot.Enclosures.Height019
