import LegendreK6.M2PilotDefinitions
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp

/-! Generated proposals: every bound is checked by Lean, not by trusting Arb. -/
namespace LegendreK6.M2Pilot.Enclosures.Height027
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem height_z_bounds_2705 : ((12260065879357 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2705 / 64 : ℚ) : ℝ) ∧
    heightZ ((2705 / 64 : ℚ) : ℝ) ≤ ((191563529365 / 288230376151711744 : ℚ) : ℝ) := by
  have h : ((12260065879357 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2705 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2387 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2705 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2387 / 192 : ℚ) : ℝ) ≤ ((191563529365 / 288230376151711744 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2705 : ((4205561 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2705 / 64 : ℚ) : ℝ) ∧
    logKernel ((2705 / 64 : ℚ) : ℝ) ≤ ((2102783 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2705
  constructor
  · exact (show ((4205561 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((12260065879357 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2705 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((191563529365 / 288230376151711744 : ℚ) : ℝ) ≤ ((2102783 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2706 : ((6034995587839 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((1353 / 32 : ℚ) : ℝ) ∧
    heightZ ((1353 / 32 : ℚ) : ℝ) ≤ ((12069991175681 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((6034995587839 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((1353 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1195 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1353 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1195 / 96 : ℚ) : ℝ) ≤ ((12069991175681 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2706 : ((4076169 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1353 / 32 : ℚ) : ℝ) ∧
    logKernel ((1353 / 32 : ℚ) : ℝ) ≤ ((2038087 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2706
  constructor
  · exact (show ((4076169 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((6034995587839 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1353 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((12069991175681 / 18446744073709551616 : ℚ) : ℝ) ≤ ((2038087 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2707 : ((5941431653571 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2707 / 64 : ℚ) : ℝ) ∧
    heightZ ((2707 / 64 : ℚ) : ℝ) ≤ ((11882863307145 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((5941431653571 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2707 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2393 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2707 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2393 / 192 : ℚ) : ℝ) ≤ ((11882863307145 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2707 : ((3950759 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2707 / 64 : ℚ) : ℝ) ∧
    logKernel ((2707 / 64 : ℚ) : ℝ) ≤ ((987691 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2707
  constructor
  · exact (show ((3950759 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((5941431653571 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2707 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((11882863307145 / 18446744073709551616 : ℚ) : ℝ) ≤ ((987691 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2708 : ((1462329573413 / 2305843009213693952 : ℚ) : ℝ) ≤ heightZ ((677 / 16 : ℚ) : ℝ) ∧
    heightZ ((677 / 16 : ℚ) : ℝ) ≤ ((11698636587307 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((1462329573413 / 2305843009213693952 : ℚ) : ℝ) ≤ Real.exp (-((677 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-599 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((677 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-599 / 48 : ℚ) : ℝ) ≤ ((11698636587307 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2708 : ((1914603 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((677 / 16 : ℚ) : ℝ) ∧
    logKernel ((677 / 16 : ℚ) : ℝ) ≤ ((3829211 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2708
  constructor
  · exact (show ((1914603 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((1462329573413 / 2305843009213693952 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((677 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((11698636587307 / 18446744073709551616 : ℚ) : ℝ) ≤ ((3829211 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2709 : ((5758633019011 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2709 / 64 : ℚ) : ℝ) ∧
    heightZ ((2709 / 64 : ℚ) : ℝ) ≤ ((11517266038025 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((5758633019011 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2709 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2399 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2709 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2399 / 192 : ℚ) : ℝ) ≤ ((11517266038025 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2709 : ((1855697 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2709 / 64 : ℚ) : ℝ) ∧
    logKernel ((2709 / 64 : ℚ) : ℝ) ≤ ((3711399 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2709
  constructor
  · exact (show ((1855697 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((5758633019011 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2709 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((11517266038025 / 18446744073709551616 : ℚ) : ℝ) ≤ ((3711399 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2710 : ((2834676844619 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((1355 / 32 : ℚ) : ℝ) ∧
    heightZ ((1355 / 32 : ℚ) : ℝ) ≤ ((11338707378479 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((2834676844619 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((1355 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1201 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1355 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1201 / 96 : ℚ) : ℝ) ≤ ((11338707378479 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2710 : ((1798603 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((1355 / 32 : ℚ) : ℝ) ∧
    logKernel ((1355 / 32 : ℚ) : ℝ) ≤ ((3597211 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2710
  constructor
  · exact (show ((1798603 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((2834676844619 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1355 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((11338707378479 / 18446744073709551616 : ℚ) : ℝ) ≤ ((3597211 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2711 : ((2790729253589 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((2711 / 64 : ℚ) : ℝ) ∧
    heightZ ((2711 / 64 : ℚ) : ℝ) ≤ ((11162917014359 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((2790729253589 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((2711 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2405 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2711 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2405 / 192 : ℚ) : ℝ) ≤ ((11162917014359 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2711 : ((871633 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((2711 / 64 : ℚ) : ℝ) ∧
    logKernel ((2711 / 64 : ℚ) : ℝ) ≤ ((3486537 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2711
  constructor
  · exact (show ((871633 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((2790729253589 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2711 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((11162917014359 / 18446744073709551616 : ℚ) : ℝ) ≤ ((3486537 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2712 : ((10989852027221 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((339 / 8 : ℚ) : ℝ) ∧
    heightZ ((339 / 8 : ℚ) : ℝ) ≤ ((1373731503403 / 2305843009213693952 : ℚ) : ℝ) := by
  have h : ((10989852027221 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((339 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-301 / 24 : ℚ) : ℝ) ∧
      Real.exp (-((339 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-301 / 24 : ℚ) : ℝ) ≤ ((1373731503403 / 2305843009213693952 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2712 : ((3379263 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((339 / 8 : ℚ) : ℝ) ∧
    logKernel ((339 / 8 : ℚ) : ℝ) ≤ ((844817 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2712
  constructor
  · exact (show ((3379263 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((10989852027221 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((339 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1373731503403 / 2305843009213693952 : ℚ) : ℝ) ≤ ((844817 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2713 : ((10819470164015 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2713 / 64 : ℚ) : ℝ) ∧
    heightZ ((2713 / 64 : ℚ) : ℝ) ≤ ((5409735082009 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((10819470164015 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2713 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2411 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2713 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2411 / 192 : ℚ) : ℝ) ≤ ((5409735082009 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2713 : ((3275293 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2713 / 64 : ℚ) : ℝ) ∧
    logKernel ((2713 / 64 : ℚ) : ℝ) ≤ ((1637649 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2713
  constructor
  · exact (show ((3275293 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((10819470164015 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2713 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((5409735082009 / 9223372036854775808 : ℚ) : ℝ) ≤ ((1637649 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2714 : ((10651729826759 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1357 / 32 : ℚ) : ℝ) ∧
    heightZ ((1357 / 32 : ℚ) : ℝ) ≤ ((5325864913381 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((10651729826759 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1357 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1207 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1357 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1207 / 96 : ℚ) : ℝ) ≤ ((5325864913381 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2714 : ((3174523 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1357 / 32 : ℚ) : ℝ) ∧
    logKernel ((1357 / 32 : ℚ) : ℝ) ≤ ((24801 / 562949953421312 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2714
  constructor
  · exact (show ((3174523 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((10651729826759 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1357 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((5325864913381 / 9223372036854775808 : ℚ) : ℝ) ≤ ((24801 / 562949953421312 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2715 : ((10486590062389 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2715 / 64 : ℚ) : ℝ) ∧
    heightZ ((2715 / 64 : ℚ) : ℝ) ≤ ((1310823757799 / 2305843009213693952 : ℚ) : ℝ) := by
  have h : ((10486590062389 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2715 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2417 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2715 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2417 / 192 : ℚ) : ℝ) ≤ ((1310823757799 / 2305843009213693952 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2715 : ((3076853 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2715 / 64 : ℚ) : ℝ) ∧
    logKernel ((2715 / 64 : ℚ) : ℝ) ≤ ((1538429 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2715
  constructor
  · exact (show ((3076853 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((10486590062389 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2715 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1310823757799 / 2305843009213693952 : ℚ) : ℝ) ≤ ((1538429 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2716 : ((5162005276379 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((679 / 16 : ℚ) : ℝ) ∧
    heightZ ((679 / 16 : ℚ) : ℝ) ≤ ((10324010552761 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((5162005276379 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((679 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-605 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((679 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-605 / 48 : ℚ) : ℝ) ≤ ((10324010552761 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2716 : ((745547 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((679 / 16 : ℚ) : ℝ) ∧
    logKernel ((679 / 16 : ℚ) : ℝ) ≤ ((2982193 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2716
  constructor
  · exact (show ((745547 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((5162005276379 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((679 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((10324010552761 / 18446744073709551616 : ℚ) : ℝ) ≤ ((2982193 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2717 : ((10163951604797 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2717 / 64 : ℚ) : ℝ) ∧
    heightZ ((2717 / 64 : ℚ) : ℝ) ≤ ((158811743825 / 288230376151711744 : ℚ) : ℝ) := by
  have h : ((10163951604797 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2717 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2423 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2717 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2423 / 192 : ℚ) : ℝ) ≤ ((158811743825 / 288230376151711744 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2717 : ((722609 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((2717 / 64 : ℚ) : ℝ) ∧
    logKernel ((2717 / 64 : ℚ) : ℝ) ≤ ((2890441 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2717
  constructor
  · exact (show ((722609 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((10163951604797 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2717 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((158811743825 / 288230376151711744 : ℚ) : ℝ) ≤ ((2890441 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2718 : ((5003187070409 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((1359 / 32 : ℚ) : ℝ) ∧
    heightZ ((1359 / 32 : ℚ) : ℝ) ≤ ((10006374140821 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((5003187070409 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((1359 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1213 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1359 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1213 / 96 : ℚ) : ℝ) ≤ ((10006374140821 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2718 : ((2801507 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1359 / 32 : ℚ) : ℝ) ∧
    logKernel ((1359 / 32 : ℚ) : ℝ) ≤ ((350189 / 9007199254740992 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2718
  constructor
  · exact (show ((2801507 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((5003187070409 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1359 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((10006374140821 / 18446744073709551616 : ℚ) : ℝ) ≤ ((350189 / 9007199254740992 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2719 : ((4925619844489 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2719 / 64 : ℚ) : ℝ) ∧
    heightZ ((2719 / 64 : ℚ) : ℝ) ≤ ((9851239688981 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((4925619844489 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2719 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2429 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2719 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2429 / 192 : ℚ) : ℝ) ≤ ((9851239688981 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2719 : ((2715313 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2719 / 64 : ℚ) : ℝ) ∧
    logKernel ((2719 / 64 : ℚ) : ℝ) ≤ ((1357659 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2719
  constructor
  · exact (show ((2715313 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((4925619844489 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2719 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((9851239688981 / 18446744073709551616 : ℚ) : ℝ) ≤ ((1357659 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2720 : ((9698510373885 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((85 / 2 : ℚ) : ℝ) ∧
    heightZ ((85 / 2 : ℚ) : ℝ) ≤ ((9471201537 / 18014398509481984 : ℚ) : ℝ) := by
  have h : ((9698510373885 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((85 / 2 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-38 / 3 : ℚ) : ℝ) ∧
      Real.exp (-((85 / 2 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-38 / 3 : ℚ) : ℝ) ≤ ((9471201537 / 18014398509481984 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2720 : ((657943 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((85 / 2 : ℚ) : ℝ) ∧
    logKernel ((85 / 2 : ℚ) : ℝ) ≤ ((2631777 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2720
  constructor
  · exact (show ((657943 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((9698510373885 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((85 / 2 : ℚ) : ℝ)) hh).trans
      (show zKernel ((9471201537 / 18014398509481984 : ℚ) : ℝ) ≤ ((2631777 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2721 : ((4774074453675 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2721 / 64 : ℚ) : ℝ) ∧
    heightZ ((2721 / 64 : ℚ) : ℝ) ≤ ((9548148907353 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((4774074453675 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2721 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2435 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2721 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2435 / 192 : ℚ) : ℝ) ≤ ((9548148907353 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2721 : ((2550801 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2721 / 64 : ℚ) : ℝ) ∧
    logKernel ((2721 / 64 : ℚ) : ℝ) ≤ ((1275403 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2721
  constructor
  · exact (show ((2550801 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((4774074453675 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2721 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((9548148907353 / 18446744073709551616 : ℚ) : ℝ) ≤ ((1275403 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2722 : ((9400118579283 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1361 / 32 : ℚ) : ℝ) ∧
    heightZ ((1361 / 32 : ℚ) : ℝ) ≤ ((4700059289643 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((9400118579283 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1361 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1219 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1361 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1219 / 96 : ℚ) : ℝ) ≤ ((4700059289643 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2722 : ((2472321 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1361 / 32 : ℚ) : ℝ) ∧
    logKernel ((1361 / 32 : ℚ) : ℝ) ≤ ((1236163 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2722
  constructor
  · exact (show ((2472321 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((9400118579283 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1361 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((4700059289643 / 9223372036854775808 : ℚ) : ℝ) ≤ ((1236163 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2723 : ((2313595812183 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((2723 / 64 : ℚ) : ℝ) ∧
    heightZ ((2723 / 64 : ℚ) : ℝ) ≤ ((9254383248735 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((2313595812183 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((2723 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2441 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2723 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2441 / 192 : ℚ) : ℝ) ≤ ((9254383248735 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2723 : ((2396255 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2723 / 64 : ℚ) : ℝ) ∧
    logKernel ((2723 / 64 : ℚ) : ℝ) ≤ ((599065 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2723
  constructor
  · exact (show ((2396255 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((2313595812183 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2723 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((9254383248735 / 18446744073709551616 : ℚ) : ℝ) ≤ ((599065 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2724 : ((2277726833765 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((681 / 16 : ℚ) : ℝ) ∧
    heightZ ((681 / 16 : ℚ) : ℝ) ≤ ((9110907335063 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((2277726833765 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((681 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-611 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((681 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-611 / 48 : ℚ) : ℝ) ≤ ((9110907335063 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2724 : ((1161265 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((681 / 16 : ℚ) : ℝ) ∧
    logKernel ((681 / 16 : ℚ) : ℝ) ≤ ((2322535 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2724
  constructor
  · exact (show ((1161265 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((2277726833765 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((681 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((9110907335063 / 18446744073709551616 : ℚ) : ℝ) ≤ ((2322535 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2725 : ((8969655809253 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2725 / 64 : ℚ) : ℝ) ∧
    heightZ ((2725 / 64 : ℚ) : ℝ) ≤ ((1121206976157 / 2305843009213693952 : ℚ) : ℝ) := by
  have h : ((8969655809253 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2725 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2447 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2725 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2447 / 192 : ℚ) : ℝ) ≤ ((1121206976157 / 2305843009213693952 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2725 : ((2251073 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2725 / 64 : ℚ) : ℝ) ∧
    logKernel ((2725 / 64 : ℚ) : ℝ) ≤ ((1125539 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2725
  constructor
  · exact (show ((2251073 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((8969655809253 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2725 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1121206976157 / 2305843009213693952 : ℚ) : ℝ) ≤ ((1125539 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2726 : ((4415297092687 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((1363 / 32 : ℚ) : ℝ) ∧
    heightZ ((1363 / 32 : ℚ) : ℝ) ≤ ((8830594185377 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((4415297092687 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((1363 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1225 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1363 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1225 / 96 : ℚ) : ℝ) ≤ ((8830594185377 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2726 : ((2181815 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1363 / 32 : ℚ) : ℝ) ∧
    logKernel ((1363 / 32 : ℚ) : ℝ) ≤ ((545455 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2726
  constructor
  · exact (show ((2181815 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((4415297092687 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1363 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((8830594185377 / 18446744073709551616 : ℚ) : ℝ) ≤ ((545455 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2727 : ((8693688512141 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2727 / 64 : ℚ) : ℝ) ∧
    heightZ ((2727 / 64 : ℚ) : ℝ) ≤ ((543355532009 / 1152921504606846976 : ℚ) : ℝ) := by
  have h : ((8693688512141 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2727 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2453 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2727 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2453 / 192 : ℚ) : ℝ) ≤ ((543355532009 / 1152921504606846976 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2727 : ((16521 / 562949953421312 : ℚ) : ℝ) ≤ logKernel ((2727 / 64 : ℚ) : ℝ) ∧
    logKernel ((2727 / 64 : ℚ) : ℝ) ≤ ((2114693 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2727
  constructor
  · exact (show ((16521 / 562949953421312 : ℚ) : ℝ) ≤ zKernel ((8693688512141 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2727 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((543355532009 / 1152921504606846976 : ℚ) : ℝ) ≤ ((2114693 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2728 : ((4279452682319 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((341 / 8 : ℚ) : ℝ) ∧
    heightZ ((341 / 8 : ℚ) : ℝ) ≤ ((8558905364641 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((4279452682319 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((341 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-307 / 24 : ℚ) : ℝ) ∧
      Real.exp (-((341 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-307 / 24 : ℚ) : ℝ) ≤ ((8558905364641 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2728 : ((2049625 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((341 / 8 : ℚ) : ℝ) ∧
    logKernel ((341 / 8 : ℚ) : ℝ) ≤ ((1024815 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2728
  constructor
  · exact (show ((2049625 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((4279452682319 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((341 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((8558905364641 / 18446744073709551616 : ℚ) : ℝ) ≤ ((1024815 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2729 : ((8426211836153 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2729 / 64 : ℚ) : ℝ) ∧
    heightZ ((2729 / 64 : ℚ) : ℝ) ≤ ((2106552959039 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((8426211836153 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2729 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2459 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2729 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2459 / 192 : ℚ) : ℝ) ≤ ((2106552959039 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2729 : ((1986565 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2729 / 64 : ℚ) : ℝ) ∧
    logKernel ((2729 / 64 : ℚ) : ℝ) ≤ ((993285 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2729
  constructor
  · exact (show ((1986565 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((8426211836153 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2729 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((2106552959039 / 4611686018427387904 : ℚ) : ℝ) ≤ ((993285 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2730 : ((8295575530145 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1365 / 32 : ℚ) : ℝ) ∧
    heightZ ((1365 / 32 : ℚ) : ℝ) ≤ ((2073893882537 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((8295575530145 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1365 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1231 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1365 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1231 / 96 : ℚ) : ℝ) ≤ ((2073893882537 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2730 : ((1925445 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1365 / 32 : ℚ) : ℝ) ∧
    logKernel ((1365 / 32 : ℚ) : ℝ) ≤ ((962725 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2730
  constructor
  · exact (show ((1925445 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((8295575530145 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1365 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((2073893882537 / 4611686018427387904 : ℚ) : ℝ) ≤ ((962725 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2731 : ((8166964552337 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2731 / 64 : ℚ) : ℝ) ∧
    heightZ ((2731 / 64 : ℚ) : ℝ) ≤ ((2041741138085 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((8166964552337 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2731 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2465 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2731 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2465 / 192 : ℚ) : ℝ) ≤ ((2041741138085 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2731 : ((1866205 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2731 / 64 : ℚ) : ℝ) ∧
    logKernel ((2731 / 64 : ℚ) : ℝ) ≤ ((933105 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2731
  constructor
  · exact (show ((1866205 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((8166964552337 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2731 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((2041741138085 / 4611686018427387904 : ℚ) : ℝ) ≤ ((933105 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2732 : ((8040347502925 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((683 / 16 : ℚ) : ℝ) ∧
    heightZ ((683 / 16 : ℚ) : ℝ) ≤ ((502521718933 / 1152921504606846976 : ℚ) : ℝ) := by
  have h : ((8040347502925 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((683 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-617 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((683 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-617 / 48 : ℚ) : ℝ) ≤ ((502521718933 / 1152921504606846976 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2732 : ((452197 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((683 / 16 : ℚ) : ℝ) ∧
    logKernel ((683 / 16 : ℚ) : ℝ) ≤ ((1808793 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2732
  constructor
  · exact (show ((452197 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((8040347502925 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((683 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((502521718933 / 1152921504606846976 : ℚ) : ℝ) ≤ ((1808793 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2733 : ((7915693468915 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2733 / 64 : ℚ) : ℝ) ∧
    heightZ ((2733 / 64 : ℚ) : ℝ) ≤ ((3957846734459 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((7915693468915 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2733 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2471 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2733 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2471 / 192 : ℚ) : ℝ) ≤ ((3957846734459 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2733 : ((1753137 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2733 / 64 : ℚ) : ℝ) ∧
    logKernel ((2733 / 64 : ℚ) : ℝ) ≤ ((876571 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2733
  constructor
  · exact (show ((1753137 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((7915693468915 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2733 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((3957846734459 / 9223372036854775808 : ℚ) : ℝ) ≤ ((876571 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2734 : ((3896486008287 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((1367 / 32 : ℚ) : ℝ) ∧
    heightZ ((1367 / 32 : ℚ) : ℝ) ≤ ((7792972016577 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((3896486008287 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((1367 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1237 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1367 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1237 / 96 : ℚ) : ℝ) ≤ ((7792972016577 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2734 : ((1699199 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1367 / 32 : ℚ) : ℝ) ∧
    logKernel ((1367 / 32 : ℚ) : ℝ) ≤ ((424801 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2734
  constructor
  · exact (show ((1699199 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((3896486008287 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1367 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((7792972016577 / 18446744073709551616 : ℚ) : ℝ) ≤ ((424801 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2735 : ((29969348375 / 72057594037927936 : ℚ) : ℝ) ≤ heightZ ((2735 / 64 : ℚ) : ℝ) ∧
    heightZ ((2735 / 64 : ℚ) : ℝ) ≤ ((7672153184003 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((29969348375 / 72057594037927936 : ℚ) : ℝ) ≤ Real.exp (-((2735 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2477 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2735 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2477 / 192 : ℚ) : ℝ) ≤ ((7672153184003 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2735 : ((205865 / 9007199254740992 : ℚ) : ℝ) ≤ logKernel ((2735 / 64 : ℚ) : ℝ) ∧
    logKernel ((2735 / 64 : ℚ) : ℝ) ≤ ((1646925 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2735
  constructor
  · exact (show ((205865 / 9007199254740992 : ℚ) : ℝ) ≤ zKernel ((29969348375 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2735 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((7672153184003 / 18446744073709551616 : ℚ) : ℝ) ≤ ((1646925 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2736 : ((472075467113 / 1152921504606846976 : ℚ) : ℝ) ≤ heightZ ((171 / 4 : ℚ) : ℝ) ∧
    heightZ ((171 / 4 : ℚ) : ℝ) ≤ ((7553207473811 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((472075467113 / 1152921504606846976 : ℚ) : ℝ) ≤ Real.exp (-((171 / 4 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-155 / 12 : ℚ) : ℝ) ∧
      Real.exp (-((171 / 4 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-155 / 12 : ℚ) : ℝ) ≤ ((7553207473811 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2736 : ((1596249 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((171 / 4 : ℚ) : ℝ) ∧
    logKernel ((171 / 4 : ℚ) : ℝ) ≤ ((798127 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2736
  constructor
  · exact (show ((1596249 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((472075467113 / 1152921504606846976 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((171 / 4 : ℚ) : ℝ)) hh).trans
      (show zKernel ((7553207473811 / 18446744073709551616 : ℚ) : ℝ) ≤ ((798127 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2737 : ((3718052922963 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2737 / 64 : ℚ) : ℝ) ∧
    heightZ ((2737 / 64 : ℚ) : ℝ) ≤ ((7436105845929 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((3718052922963 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2737 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2483 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2737 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2483 / 192 : ℚ) : ℝ) ≤ ((7436105845929 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2737 : ((773569 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2737 / 64 : ℚ) : ℝ) ∧
    logKernel ((2737 / 64 : ℚ) : ℝ) ≤ ((1547143 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2737
  constructor
  · exact (show ((773569 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((3718052922963 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2737 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((7436105845929 / 18446744073709551616 : ℚ) : ℝ) ≤ ((1547143 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem log_height_bounds_864 : ((67452100025312669 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((1353 / 32 : ℚ) : ℝ) ∧
    Real.log ((1353 / 32 : ℚ) : ℝ) ≤ ((269808400101250679 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((67452100025312669 / 18014398509481984 : ℚ) : ℝ) ≤ ((1353 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1353 / 32 : ℚ) : ℝ) ≤ Real.exp ((269808400101250679 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_864 : heightPower (864 : Fin 988) ≤ ((488533906075251 / 35184372088832 : ℚ) : ℝ) := by
  have hh := log_height_bounds_864
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_864 : heightFactor (864 : Fin 988) ≤ ((5781635 / 8796093022208 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_864
  obtain ⟨hpl, hph⟩ := kernel_bounds_2705
  obtain ⟨hcl, hch⟩ := kernel_bounds_2706
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2706
  have h : (((1830609 / 512 : ℚ) : ℝ) * (logKernel ((2705 / 64 : ℚ) : ℝ) - logKernel ((1353 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1353 / 32 : ℚ) : ℝ) + Real.log ((1353 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((5781635 / 8796093022208 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_865 : ((134917512002381791 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2707 / 64 : ℚ) : ℝ) ∧
    Real.log ((2707 / 64 : ℚ) : ℝ) ≤ ((269835024004763585 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((134917512002381791 / 36028797018963968 : ℚ) : ℝ) ≤ ((2707 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2707 / 64 : ℚ) : ℝ) ≤ Real.exp ((269835024004763585 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_865 : heightPower (865 : Fin 988) ≤ ((3912773294736209 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_865
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_865 : heightFactor (865 : Fin 988) ≤ ((11275849 / 17592186044416 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_865
  obtain ⟨hpl, hph⟩ := kernel_bounds_2706
  obtain ⟨hcl, hch⟩ := kernel_bounds_2707
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2707
  have h : (((7327849 / 2048 : ℚ) : ℝ) * (logKernel ((1353 / 32 : ℚ) : ℝ) - logKernel ((2707 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2707 / 64 : ℚ) : ℝ) + Real.log ((2707 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((11275849 / 17592186044416 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_866 : ((33732704759360779 / 9007199254740992 : ℚ) : ℝ) ≤ Real.log ((677 / 16 : ℚ) : ℝ) ∧
    Real.log ((677 / 16 : ℚ) : ℝ) ≤ ((269861638074886235 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((33732704759360779 / 9007199254740992 : ℚ) : ℝ) ≤ ((677 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((677 / 16 : ℚ) : ℝ) ≤ Real.exp ((269861638074886235 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_866 : heightPower (866 : Fin 988) ≤ ((1958637651229365 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_866
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_866 : heightFactor (866 : Fin 988) ≤ ((175929141 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_866
  obtain ⟨hpl, hph⟩ := kernel_bounds_2707
  obtain ⟨hcl, hch⟩ := kernel_bounds_2708
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2708
  have h : (((458329 / 128 : ℚ) : ℝ) * (logKernel ((2707 / 64 : ℚ) : ℝ) - logKernel ((677 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((677 / 16 : ℚ) : ℝ) + Real.log ((677 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((175929141 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_867 : ((269888242318879759 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2709 / 64 : ℚ) : ℝ) ∧
    Real.log ((2709 / 64 : ℚ) : ℝ) ≤ ((134944121159439881 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((269888242318879759 / 72057594037927936 : ℚ) : ℝ) ≤ ((2709 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2709 / 64 : ℚ) : ℝ) ≤ Real.exp ((134944121159439881 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_867 : heightPower (867 : Fin 988) ≤ ((1960888635898967 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_867
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_867 : heightFactor (867 : Fin 988) ≤ ((171556151 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_867
  obtain ⟨hpl, hph⟩ := kernel_bounds_2708
  obtain ⟨hcl, hch⟩ := kernel_bounds_2709
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2709
  have h : (((7338681 / 2048 : ℚ) : ℝ) * (logKernel ((677 / 16 : ℚ) : ℝ) - logKernel ((2709 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2709 / 64 : ℚ) : ℝ) + Real.log ((2709 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((171556151 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_868 : ((269914836743997259 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1355 / 32 : ℚ) : ℝ) ∧
    Real.log ((1355 / 32 : ℚ) : ℝ) ≤ ((134957418371998631 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((269914836743997259 / 72057594037927936 : ℚ) : ℝ) ≤ ((1355 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1355 / 32 : ℚ) : ℝ) ≤ Real.exp ((134957418371998631 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_868 : heightPower (868 : Fin 988) ≤ ((3926279202782153 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_868
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_868 : heightFactor (868 : Fin 988) ≤ ((167291845 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_868
  obtain ⟨hpl, hph⟩ := kernel_bounds_2709
  obtain ⟨hcl, hch⟩ := kernel_bounds_2710
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2710
  have h : (((1836025 / 512 : ℚ) : ℝ) * (logKernel ((2709 / 64 : ℚ) : ℝ) - logKernel ((1355 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1355 / 32 : ℚ) : ℝ) + Real.log ((1355 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((167291845 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_869 : ((134970710678741899 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2711 / 64 : ℚ) : ℝ) ∧
    Real.log ((2711 / 64 : ℚ) : ℝ) ≤ ((269941421357483801 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((134970710678741899 / 36028797018963968 : ℚ) : ℝ) ≤ ((2711 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2711 / 64 : ℚ) : ℝ) ≤ Real.exp ((269941421357483801 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_869 : heightPower (869 : Fin 988) ≤ ((3930781095439689 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_869
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_869 : heightFactor (869 : Fin 988) ≤ ((163133525 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_869
  obtain ⟨hpl, hph⟩ := kernel_bounds_2710
  obtain ⟨hcl, hch⟩ := kernel_bounds_2711
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2711
  have h : (((7349521 / 2048 : ℚ) : ℝ) * (logKernel ((1355 / 32 : ℚ) : ℝ) - logKernel ((2711 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2711 / 64 : ℚ) : ℝ) + Real.log ((2711 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((163133525 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_870 : ((269967996166576425 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((339 / 8 : ℚ) : ℝ) ∧
    Real.log ((339 / 8 : ℚ) : ℝ) ≤ ((67491999041644107 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((269967996166576425 / 72057594037927936 : ℚ) : ℝ) ≤ ((339 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((339 / 8 : ℚ) : ℝ) ≤ Real.exp ((67491999041644107 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_870 : heightPower (870 : Fin 988) ≤ ((3935282949798811 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_870
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_870 : heightFactor (870 : Fin 988) ≤ ((159078557 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_870
  obtain ⟨hpl, hph⟩ := kernel_bounds_2711
  obtain ⟨hcl, hch⟩ := kernel_bounds_2712
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2712
  have h : (((114921 / 32 : ℚ) : ℝ) * (logKernel ((2711 / 64 : ℚ) : ℝ) - logKernel ((339 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((339 / 8 : ℚ) : ℝ) + Real.log ((339 / 8 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((159078557 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_871 : ((67498640294626047 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((2713 / 64 : ℚ) : ℝ) ∧
    Real.log ((2713 / 64 : ℚ) : ℝ) ≤ ((269994561178504191 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((67498640294626047 / 18014398509481984 : ℚ) : ℝ) ≤ ((2713 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2713 / 64 : ℚ) : ℝ) ≤ Real.exp ((269994561178504191 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_871 : heightPower (871 : Fin 988) ≤ ((3939784765887757 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_871
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_871 : heightFactor (871 : Fin 988) ≤ ((155124373 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_871
  obtain ⟨hpl, hph⟩ := kernel_bounds_2712
  obtain ⟨hcl, hch⟩ := kernel_bounds_2713
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2713
  have h : (((7360369 / 2048 : ℚ) : ℝ) * (logKernel ((339 / 8 : ℚ) : ℝ) - logKernel ((2713 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2713 / 64 : ℚ) : ℝ) + Real.log ((2713 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((155124373 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_872 : ((270021116400488141 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1357 / 32 : ℚ) : ℝ) ∧
    Real.log ((1357 / 32 : ℚ) : ℝ) ≤ ((16876319775030509 / 4503599627370496 : ℚ) : ℝ) := by
  have hl : Real.exp ((270021116400488141 / 72057594037927936 : ℚ) : ℝ) ≤ ((1357 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1357 / 32 : ℚ) : ℝ) ≤ Real.exp ((16876319775030509 / 4503599627370496 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_872 : heightPower (872 : Fin 988) ≤ ((246517908983421 / 17592186044416 : ℚ) : ℝ) := by
  have hh := log_height_bounds_872
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_872 : heightFactor (872 : Fin 988) ≤ ((75634235 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_872
  obtain ⟨hpl, hph⟩ := kernel_bounds_2713
  obtain ⟨hcl, hch⟩ := kernel_bounds_2714
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2714
  have h : (((1841449 / 512 : ℚ) : ℝ) * (logKernel ((2713 / 64 : ℚ) : ℝ) - logKernel ((1357 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1357 / 32 : ℚ) : ℝ) + Real.log ((1357 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((75634235 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_873 : ((270047661839741357 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2715 / 64 : ℚ) : ℝ) ∧
    Real.log ((2715 / 64 : ℚ) : ℝ) ≤ ((16877978864983835 / 4503599627370496 : ℚ) : ℝ) := by
  have hl : Real.exp ((270047661839741357 / 72057594037927936 : ℚ) : ℝ) ≤ ((2715 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2715 / 64 : ℚ) : ℝ) ≤ Real.exp ((16877978864983835 / 4503599627370496 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_873 : heightPower (873 : Fin 988) ≤ ((3948788283367923 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_873
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_873 : heightFactor (873 : Fin 988) ≤ ((147508407 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_873
  obtain ⟨hpl, hph⟩ := kernel_bounds_2714
  obtain ⟨hcl, hch⟩ := kernel_bounds_2715
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2715
  have h : (((7371225 / 2048 : ℚ) : ℝ) * (logKernel ((1357 / 32 : ℚ) : ℝ) - logKernel ((2715 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2715 / 64 : ℚ) : ℝ) + Real.log ((2715 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((147508407 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_874 : ((270074197503468941 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((679 / 16 : ℚ) : ℝ) ∧
    Real.log ((679 / 16 : ℚ) : ℝ) ≤ ((16879637343966809 / 4503599627370496 : ℚ) : ℝ) := by
  have hl : Real.exp ((270074197503468941 / 72057594037927936 : ℚ) : ℝ) ≤ ((679 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((679 / 16 : ℚ) : ℝ) ≤ Real.exp ((16879637343966809 / 4503599627370496 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_874 : heightPower (874 : Fin 988) ≤ ((3953289984815463 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_874
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_874 : heightFactor (874 : Fin 988) ≤ ((71920901 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_874
  obtain ⟨hpl, hph⟩ := kernel_bounds_2715
  obtain ⟨hcl, hch⟩ := kernel_bounds_2716
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2716
  have h : (((461041 / 128 : ℚ) : ℝ) * (logKernel ((2715 / 64 : ℚ) : ℝ) - logKernel ((679 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((679 / 16 : ℚ) : ℝ) + Real.log ((679 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((71920901 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_875 : ((135050361699434021 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2717 / 64 : ℚ) : ℝ) ∧
    Real.log ((2717 / 64 : ℚ) : ℝ) ≤ ((270100723398868045 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((135050361699434021 / 36028797018963968 : ℚ) : ℝ) ≤ ((2717 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2717 / 64 : ℚ) : ℝ) ≤ Real.exp ((270100723398868045 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_875 : heightPower (875 : Fin 988) ≤ ((1978895824052735 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_875
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_875 : heightFactor (875 : Fin 988) ≤ ((70133167 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_875
  obtain ⟨hpl, hph⟩ := kernel_bounds_2716
  obtain ⟨hcl, hch⟩ := kernel_bounds_2717
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2717
  have h : (((7382089 / 2048 : ℚ) : ℝ) * (logKernel ((679 / 16 : ℚ) : ℝ) - logKernel ((2717 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2717 / 64 : ℚ) : ℝ) + Real.log ((2717 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((70133167 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_876 : ((67531809883281965 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((1359 / 32 : ℚ) : ℝ) ∧
    Real.log ((1359 / 32 : ℚ) : ℝ) ≤ ((270127239533127863 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((67531809883281965 / 18014398509481984 : ℚ) : ℝ) ≤ ((1359 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1359 / 32 : ℚ) : ℝ) ≤ Real.exp ((270127239533127863 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_876 : heightPower (876 : Fin 988) ≤ ((1981146636633013 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_876
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_876 : heightFactor (876 : Fin 988) ≤ ((68389869 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_876
  obtain ⟨hpl, hph⟩ := kernel_bounds_2717
  obtain ⟨hcl, hch⟩ := kernel_bounds_2718
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2718
  have h : (((1846881 / 512 : ℚ) : ℝ) * (logKernel ((2717 / 64 : ℚ) : ℝ) - logKernel ((1359 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1359 / 32 : ℚ) : ℝ) + Real.log ((1359 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((68389869 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_877 : ((135076872956714833 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2719 / 64 : ℚ) : ℝ) ∧
    Real.log ((2719 / 64 : ℚ) : ℝ) ≤ ((270153745913429669 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((135076872956714833 / 36028797018963968 : ℚ) : ℝ) ≤ ((2719 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2719 / 64 : ℚ) : ℝ) ≤ Real.exp ((270153745913429669 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_877 : heightPower (877 : Fin 988) ≤ ((61981169692581 / 4398046511104 : ℚ) : ℝ) := by
  have hh := log_height_bounds_877
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_877 : heightFactor (877 : Fin 988) ≤ ((133379807 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_877
  obtain ⟨hpl, hph⟩ := kernel_bounds_2718
  obtain ⟨hcl, hch⟩ := kernel_bounds_2719
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2719
  have h : (((7392961 / 2048 : ℚ) : ℝ) * (logKernel ((1359 / 32 : ℚ) : ℝ) - logKernel ((2719 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2719 / 64 : ℚ) : ℝ) + Real.log ((2719 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((133379807 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_878 : ((270180242546946805 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((85 / 2 : ℚ) : ℝ) ∧
    Real.log ((85 / 2 : ℚ) : ℝ) ≤ ((33772530318368351 / 9007199254740992 : ℚ) : ℝ) := by
  have hl : Real.exp ((270180242546946805 / 72057594037927936 : ℚ) : ℝ) ≤ ((85 / 2 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((85 / 2 : ℚ) : ℝ) ≤ Real.exp ((33772530318368351 / 9007199254740992 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_878 : heightPower (878 : Fin 988) ≤ ((992824102327741 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_878
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_878 : heightFactor (878 : Fin 988) ≤ ((130064387 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_878
  obtain ⟨hpl, hph⟩ := kernel_bounds_2719
  obtain ⟨hcl, hch⟩ := kernel_bounds_2720
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2720
  have h : (((7225 / 2 : ℚ) : ℝ) * (logKernel ((2719 / 64 : ℚ) : ℝ) - logKernel ((85 / 2 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((85 / 2 : ℚ) : ℝ) + Real.log ((85 / 2 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((130064387 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_879 : ((67551682360211179 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((2721 / 64 : ℚ) : ℝ) ∧
    Real.log ((2721 / 64 : ℚ) : ℝ) ≤ ((270206729440844719 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((67551682360211179 / 18014398509481984 : ℚ) : ℝ) ≤ ((2721 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2721 / 64 : ℚ) : ℝ) ≤ Real.exp ((270206729440844719 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_879 : heightPower (879 : Fin 988) ≤ ((3975797920251357 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_879
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_879 : heightFactor (879 : Fin 988) ≤ ((31707845 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_879
  obtain ⟨hpl, hph⟩ := kernel_bounds_2720
  obtain ⟨hcl, hch⟩ := kernel_bounds_2721
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2721
  have h : (((7403841 / 2048 : ℚ) : ℝ) * (logKernel ((85 / 2 : ℚ) : ℝ) - logKernel ((2721 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2721 / 64 : ℚ) : ℝ) + Real.log ((2721 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((31707845 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_880 : ((135116603301140467 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((1361 / 32 : ℚ) : ℝ) ∧
    Real.log ((1361 / 32 : ℚ) : ℝ) ≤ ((270233206602280937 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((135116603301140467 / 36028797018963968 : ℚ) : ℝ) ≤ ((1361 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1361 / 32 : ℚ) : ℝ) ≤ Real.exp ((270233206602280937 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_880 : heightPower (880 : Fin 988) ≤ ((3980299393174321 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_880
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_880 : heightFactor (880 : Fin 988) ≤ ((7729921 / 17592186044416 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_880
  obtain ⟨hpl, hph⟩ := kernel_bounds_2721
  obtain ⟨hcl, hch⟩ := kernel_bounds_2722
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2722
  have h : (((1852321 / 512 : ℚ) : ℝ) * (logKernel ((2721 / 64 : ℚ) : ℝ) - logKernel ((1361 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1361 / 32 : ℚ) : ℝ) + Real.log ((1361 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((7729921 / 17592186044416 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_881 : ((270259674038405111 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2723 / 64 : ℚ) : ℝ) ∧
    Real.log ((2723 / 64 : ℚ) : ℝ) ≤ ((135129837019202557 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((270259674038405111 / 72057594037927936 : ℚ) : ℝ) ≤ ((2723 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2723 / 64 : ℚ) : ℝ) ≤ Real.exp ((135129837019202557 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_881 : heightPower (881 : Fin 988) ≤ ((3984800828107785 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_881
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_881 : heightFactor (881 : Fin 988) ≤ ((120604461 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_881
  obtain ⟨hpl, hph⟩ := kernel_bounds_2722
  obtain ⟨hcl, hch⟩ := kernel_bounds_2723
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2723
  have h : (((7414729 / 2048 : ℚ) : ℝ) * (logKernel ((1361 / 32 : ℚ) : ℝ) - logKernel ((2723 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2723 / 64 : ℚ) : ℝ) + Real.log ((2723 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((120604461 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_882 : ((270286131756359023 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((681 / 16 : ℚ) : ℝ) ∧
    Real.log ((681 / 16 : ℚ) : ℝ) ≤ ((135143065878179513 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((270286131756359023 / 72057594037927936 : ℚ) : ℝ) ≤ ((681 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((681 / 16 : ℚ) : ℝ) ≤ Real.exp ((135143065878179513 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_882 : heightPower (882 : Fin 988) ≤ ((3989302225079647 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_882
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_882 : heightFactor (882 : Fin 988) ≤ ((58803303 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_882
  obtain ⟨hpl, hph⟩ := kernel_bounds_2723
  obtain ⟨hcl, hch⟩ := kernel_bounds_2724
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2724
  have h : (((463761 / 128 : ℚ) : ℝ) * (logKernel ((2723 / 64 : ℚ) : ℝ) - logKernel ((681 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((681 / 16 : ℚ) : ℝ) + Real.log ((681 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((58803303 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_883 : ((67578144940819145 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((2725 / 64 : ℚ) : ℝ) ∧
    Real.log ((2725 / 64 : ℚ) : ℝ) ≤ ((270312579763276583 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((67578144940819145 / 18014398509481984 : ℚ) : ℝ) ≤ ((2725 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2725 / 64 : ℚ) : ℝ) ≤ Real.exp ((270312579763276583 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_883 : heightPower (883 : Fin 988) ≤ ((3993803584117773 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_883
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_883 : heightFactor (883 : Fin 988) ≤ ((14335409 / 35184372088832 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_883
  obtain ⟨hpl, hph⟩ := kernel_bounds_2724
  obtain ⟨hcl, hch⟩ := kernel_bounds_2725
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2725
  have h : (((7425625 / 2048 : ℚ) : ℝ) * (logKernel ((681 / 16 : ℚ) : ℝ) - logKernel ((2725 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2725 / 64 : ℚ) : ℝ) + Real.log ((2725 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((14335409 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_884 : ((270339018066283841 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1363 / 32 : ℚ) : ℝ) ∧
    Real.log ((1363 / 32 : ℚ) : ℝ) ≤ ((67584754516570961 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((270339018066283841 / 72057594037927936 : ℚ) : ℝ) ≤ ((1363 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1363 / 32 : ℚ) : ℝ) ≤ Real.exp ((67584754516570961 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_884 : heightPower (884 : Fin 988) ≤ ((3998304905249999 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_884
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_884 : heightFactor (884 : Fin 988) ≤ ((55916305 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_884
  obtain ⟨hpl, hph⟩ := kernel_bounds_2725
  obtain ⟨hcl, hch⟩ := kernel_bounds_2726
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2726
  have h : (((1857769 / 512 : ℚ) : ℝ) * (logKernel ((2725 / 64 : ℚ) : ℝ) - logKernel ((1363 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1363 / 32 : ℚ) : ℝ) + Real.log ((1363 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((55916305 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_885 : ((16897840417031189 / 4503599627370496 : ℚ) : ℝ) ≤ Real.log ((2727 / 64 : ℚ) : ℝ) ∧
    Real.log ((2727 / 64 : ℚ) : ℝ) ≤ ((270365446672499027 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((16897840417031189 / 4503599627370496 : ℚ) : ℝ) ≤ ((2727 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2727 / 64 : ℚ) : ℝ) ≤ Real.exp ((270365446672499027 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_885 : heightPower (885 : Fin 988) ≤ ((4002806188504131 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_885
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_885 : heightFactor (885 : Fin 988) ≤ ((27263203 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_885
  obtain ⟨hpl, hph⟩ := kernel_bounds_2726
  obtain ⟨hcl, hch⟩ := kernel_bounds_2727
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2727
  have h : (((7436529 / 2048 : ℚ) : ℝ) * (logKernel ((1363 / 32 : ℚ) : ℝ) - logKernel ((2727 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2727 / 64 : ℚ) : ℝ) + Real.log ((2727 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((27263203 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_886 : ((270391865589032519 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((341 / 8 : ℚ) : ℝ) ∧
    Real.log ((341 / 8 : ℚ) : ℝ) ≤ ((135195932794516261 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((270391865589032519 / 72057594037927936 : ℚ) : ℝ) ≤ ((341 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((341 / 8 : ℚ) : ℝ) ≤ Real.exp ((135195932794516261 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_886 : heightPower (886 : Fin 988) ≤ ((500913429238493 / 35184372088832 : ℚ) : ℝ) := by
  have hh := log_height_bounds_886
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_886 : heightFactor (886 : Fin 988) ≤ ((106342117 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_886
  obtain ⟨hpl, hph⟩ := kernel_bounds_2727
  obtain ⟨hcl, hch⟩ := kernel_bounds_2728
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2728
  have h : (((116281 / 32 : ℚ) : ℝ) * (logKernel ((2727 / 64 : ℚ) : ℝ) - logKernel ((341 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((341 / 8 : ℚ) : ℝ) + Real.log ((341 / 8 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((106342117 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_887 : ((135209137411493447 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2729 / 64 : ℚ) : ℝ) ∧
    Real.log ((2729 / 64 : ℚ) : ℝ) ≤ ((270418274822986897 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((135209137411493447 / 36028797018963968 : ℚ) : ℝ) ≤ ((2729 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2729 / 64 : ℚ) : ℝ) ≤ Real.exp ((270418274822986897 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_887 : heightPower (887 : Fin 988) ≤ ((2005904320744591 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_887
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_887 : heightFactor (887 : Fin 988) ≤ ((51849405 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_887
  obtain ⟨hpl, hph⟩ := kernel_bounds_2728
  obtain ⟨hcl, hch⟩ := kernel_bounds_2729
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2729
  have h : (((7447441 / 2048 : ℚ) : ℝ) * (logKernel ((341 / 8 : ℚ) : ℝ) - logKernel ((2729 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2729 / 64 : ℚ) : ℝ) + Real.log ((2729 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((51849405 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_888 : ((270444674381456915 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1365 / 32 : ℚ) : ℝ) ∧
    Real.log ((1365 / 32 : ℚ) : ℝ) ≤ ((135222337190728459 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((270444674381456915 / 72057594037927936 : ℚ) : ℝ) ≤ ((1365 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1365 / 32 : ℚ) : ℝ) ≤ Real.exp ((135222337190728459 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_888 : heightPower (888 : Fin 988) ≤ ((502038726409445 / 35184372088832 : ℚ) : ℝ) := by
  have hh := log_height_bounds_888
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_888 : heightFactor (888 : Fin 988) ≤ ((1580019 / 4398046511104 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_888
  obtain ⟨hpl, hph⟩ := kernel_bounds_2729
  obtain ⟨hcl, hch⟩ := kernel_bounds_2730
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2730
  have h : (((1863225 / 512 : ℚ) : ℝ) * (logKernel ((2729 / 64 : ℚ) : ℝ) - logKernel ((1365 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1365 / 32 : ℚ) : ℝ) + Real.log ((1365 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1580019 / 4398046511104 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_889 : ((270471064271529551 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2731 / 64 : ℚ) : ℝ) ∧
    Real.log ((2731 / 64 : ℚ) : ℝ) ≤ ((135235532135764777 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((270471064271529551 / 72057594037927936 : ℚ) : ℝ) ≤ ((2731 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2731 / 64 : ℚ) : ℝ) ≤ Real.exp ((135235532135764777 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_889 : heightPower (889 : Fin 988) ≤ ((502601367911845 / 35184372088832 : ℚ) : ℝ) := by
  have hh := log_height_bounds_889
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_889 : heightFactor (889 : Fin 988) ≤ ((98607701 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_889
  obtain ⟨hpl, hph⟩ := kernel_bounds_2730
  obtain ⟨hcl, hch⟩ := kernel_bounds_2731
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2731
  have h : (((7458361 / 2048 : ℚ) : ℝ) * (logKernel ((1365 / 32 : ℚ) : ℝ) - logKernel ((2731 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2731 / 64 : ℚ) : ℝ) + Real.log ((2731 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((98607701 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_890 : ((67624361125070997 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((683 / 16 : ℚ) : ℝ) ∧
    Real.log ((683 / 16 : ℚ) : ℝ) ≤ ((270497444500283991 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((67624361125070997 / 18014398509481984 : ℚ) : ℝ) ≤ ((683 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((683 / 16 : ℚ) : ℝ) ≤ Real.exp ((270497444500283991 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_890 : heightPower (890 : Fin 988) ≤ ((1006328009393609 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_890
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_890 : heightFactor (890 : Fin 988) ≤ ((48078337 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_890
  obtain ⟨hpl, hph⟩ := kernel_bounds_2731
  obtain ⟨hcl, hch⟩ := kernel_bounds_2732
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2732
  have h : (((466489 / 128 : ℚ) : ℝ) * (logKernel ((2731 / 64 : ℚ) : ℝ) - logKernel ((683 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((683 / 16 : ℚ) : ℝ) + Real.log ((683 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((48078337 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_891 : ((135261907537395819 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2733 / 64 : ℚ) : ℝ) ∧
    Real.log ((2733 / 64 : ℚ) : ℝ) ≤ ((270523815074791641 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((135261907537395819 / 36028797018963968 : ℚ) : ℝ) ≤ ((2733 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2733 / 64 : ℚ) : ℝ) ≤ Real.exp ((270523815074791641 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_891 : heightPower (891 : Fin 988) ≤ ((2014906547071105 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_891
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_891 : heightFactor (891 : Fin 988) ≤ ((93766581 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_891
  obtain ⟨hpl, hph⟩ := kernel_bounds_2732
  obtain ⟨hcl, hch⟩ := kernel_bounds_2733
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2733
  have h : (((7469289 / 2048 : ℚ) : ℝ) * (logKernel ((683 / 16 : ℚ) : ℝ) - logKernel ((2733 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2733 / 64 : ℚ) : ℝ) + Real.log ((2733 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((93766581 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_892 : ((135275088001058077 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((1367 / 32 : ℚ) : ℝ) ∧
    Real.log ((1367 / 32 : ℚ) : ℝ) ≤ ((270550176002116157 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((135275088001058077 / 36028797018963968 : ℚ) : ℝ) ≤ ((1367 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1367 / 32 : ℚ) : ℝ) ≤ Real.exp ((270550176002116157 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_892 : heightPower (892 : Fin 988) ≤ ((1008578528256419 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_892
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_892 : heightFactor (892 : Fin 988) ≤ ((45717955 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_892
  obtain ⟨hpl, hph⟩ := kernel_bounds_2733
  obtain ⟨hcl, hch⟩ := kernel_bounds_2734
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2734
  have h : (((1868689 / 512 : ℚ) : ℝ) * (logKernel ((2733 / 64 : ℚ) : ℝ) - logKernel ((1367 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1367 / 32 : ℚ) : ℝ) + Real.log ((1367 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((45717955 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_893 : ((8455516477791045 / 2251799813685248 : ℚ) : ℝ) ≤ Real.log ((2735 / 64 : ℚ) : ℝ) ∧
    Real.log ((2735 / 64 : ℚ) : ℝ) ≤ ((270576527289313443 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((8455516477791045 / 2251799813685248 : ℚ) : ℝ) ≤ ((2735 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2735 / 64 : ℚ) : ℝ) ≤ Real.exp ((270576527289313443 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_893 : heightPower (893 : Fin 988) ≤ ((2019407547126197 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_893
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_893 : heightFactor (893 : Fin 988) ≤ ((44581591 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_893
  obtain ⟨hpl, hph⟩ := kernel_bounds_2734
  obtain ⟨hcl, hch⟩ := kernel_bounds_2735
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2735
  have h : (((7480225 / 2048 : ℚ) : ℝ) * (logKernel ((1367 / 32 : ℚ) : ℝ) - logKernel ((2735 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2735 / 64 : ℚ) : ℝ) + Real.log ((2735 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((44581591 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_894 : ((67650717235857915 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((171 / 4 : ℚ) : ℝ) ∧
    Real.log ((171 / 4 : ℚ) : ℝ) ≤ ((270602868943431663 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((67650717235857915 / 18014398509481984 : ℚ) : ℝ) ≤ ((171 / 4 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((171 / 4 : ℚ) : ℝ) ≤ Real.exp ((270602868943431663 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_894 : heightPower (894 : Fin 988) ≤ ((4043316037849897 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_894
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_894 : heightFactor (894 : Fin 988) ≤ ((43473479 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_894
  obtain ⟨hpl, hph⟩ := kernel_bounds_2735
  obtain ⟨hcl, hch⟩ := kernel_bounds_2736
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2736
  have h : (((29241 / 8 : ℚ) : ℝ) * (logKernel ((2735 / 64 : ℚ) : ℝ) - logKernel ((171 / 4 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((171 / 4 : ℚ) : ℝ) + Real.log ((171 / 4 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((43473479 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_895 : ((270629200971511253 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2737 / 64 : ℚ) : ℝ) ∧
    Real.log ((2737 / 64 : ℚ) : ℝ) ≤ ((33828650121438907 / 9007199254740992 : ℚ) : ℝ) := by
  have hl : Real.exp ((270629200971511253 / 72057594037927936 : ℚ) : ℝ) ≤ ((2737 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2737 / 64 : ℚ) : ℝ) ≤ Real.exp ((33828650121438907 / 9007199254740992 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_895 : heightPower (895 : Fin 988) ≤ ((4047816943845687 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_895
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_895 : heightFactor (895 : Fin 988) ≤ ((84785835 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_895
  obtain ⟨hpl, hph⟩ := kernel_bounds_2736
  obtain ⟨hcl, hch⟩ := kernel_bounds_2737
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2737
  have h : (((7491169 / 2048 : ℚ) : ℝ) * (logKernel ((171 / 4 : ℚ) : ℝ) - logKernel ((2737 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2737 / 64 : ℚ) : ℝ) + Real.log ((2737 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((84785835 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

end LegendreK6.M2Pilot.Enclosures.Height027
