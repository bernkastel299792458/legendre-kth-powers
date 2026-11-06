import LegendreK6.M2PilotDefinitions
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp

/-! Generated proposals: every bound is checked by Lean, not by trusting Arb. -/
namespace LegendreK6.M2Pilot.Enclosures.Height028
set_option maxRecDepth 100000
set_option maxHeartbeats 0

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

theorem height_z_bounds_2738 : ((7320819710509 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1369 / 32 : ℚ) : ℝ) ∧
    heightZ ((1369 / 32 : ℚ) : ℝ) ≤ ((457551231907 / 1152921504606846976 : ℚ) : ℝ) := by
  have h : ((7320819710509 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1369 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1243 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1369 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1243 / 96 : ℚ) : ℝ) ≤ ((457551231907 / 1152921504606846976 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2738 : ((1499537 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1369 / 32 : ℚ) : ℝ) ∧
    logKernel ((1369 / 32 : ℚ) : ℝ) ≤ ((749771 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2738
  constructor
  · exact (show ((1499537 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((7320819710509 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1369 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((457551231907 / 1152921504606846976 : ℚ) : ℝ) ≤ ((749771 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2739 : ((7207320920955 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2739 / 64 : ℚ) : ℝ) ∧
    heightZ ((2739 / 64 : ℚ) : ℝ) ≤ ((3603660460479 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((7207320920955 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2739 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2489 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2739 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2489 / 192 : ℚ) : ℝ) ≤ ((3603660460479 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2739 : ((1453401 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2739 / 64 : ℚ) : ℝ) ∧
    logKernel ((2739 / 64 : ℚ) : ℝ) ≤ ((726703 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2739
  constructor
  · exact (show ((1453401 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((7207320920955 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2739 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((3603660460479 / 9223372036854775808 : ℚ) : ℝ) ≤ ((726703 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2740 : ((7095581767035 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((685 / 16 : ℚ) : ℝ) ∧
    heightZ ((685 / 16 : ℚ) : ℝ) ≤ ((3547790883519 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((7095581767035 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((685 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-623 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((685 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-623 / 48 : ℚ) : ℝ) ≤ ((3547790883519 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2740 : ((1408685 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((685 / 16 : ℚ) : ℝ) ∧
    logKernel ((685 / 16 : ℚ) : ℝ) ≤ ((704345 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2740
  constructor
  · exact (show ((1408685 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((7095581767035 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((685 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((3547790883519 / 9223372036854775808 : ℚ) : ℝ) ≤ ((704345 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2741 : ((6985574968127 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2741 / 64 : ℚ) : ℝ) ∧
    heightZ ((2741 / 64 : ℚ) : ℝ) ≤ ((3492787484065 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((6985574968127 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2741 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2495 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2741 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2495 / 192 : ℚ) : ℝ) ≤ ((3492787484065 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2741 : ((42667 / 2251799813685248 : ℚ) : ℝ) ≤ logKernel ((2741 / 64 : ℚ) : ℝ) ∧
    logKernel ((2741 / 64 : ℚ) : ℝ) ≤ ((1365349 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2741
  constructor
  · exact (show ((42667 / 2251799813685248 : ℚ) : ℝ) ≤ zKernel ((6985574968127 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2741 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((3492787484065 / 9223372036854775808 : ℚ) : ℝ) ≤ ((1365349 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2742 : ((6877273666555 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1371 / 32 : ℚ) : ℝ) ∧
    heightZ ((1371 / 32 : ℚ) : ℝ) ≤ ((3438636833279 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((6877273666555 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1371 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1249 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1371 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1249 / 96 : ℚ) : ℝ) ≤ ((3438636833279 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2742 : ((1323337 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1371 / 32 : ℚ) : ℝ) ∧
    logKernel ((1371 / 32 : ℚ) : ℝ) ≤ ((661671 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2742
  constructor
  · exact (show ((1323337 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((6877273666555 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1371 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((3438636833279 / 9223372036854775808 : ℚ) : ℝ) ≤ ((661671 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2743 : ((3385325710517 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2743 / 64 : ℚ) : ℝ) ∧
    heightZ ((2743 / 64 : ℚ) : ℝ) ≤ ((6770651421037 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((3385325710517 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2743 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2501 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2743 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2501 / 192 : ℚ) : ℝ) ≤ ((6770651421037 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2743 : ((641311 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2743 / 64 : ℚ) : ℝ) ∧
    logKernel ((2743 / 64 : ℚ) : ℝ) ≤ ((1282627 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2743
  constructor
  · exact (show ((641311 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((3385325710517 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2743 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((6770651421037 / 18446744073709551616 : ℚ) : ℝ) ≤ ((1282627 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2744 : ((3332841100107 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((343 / 8 : ℚ) : ℝ) ∧
    heightZ ((343 / 8 : ℚ) : ℝ) ≤ ((6665682200217 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((3332841100107 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((343 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-313 / 24 : ℚ) : ℝ) ∧
      Real.exp (-((343 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-313 / 24 : ℚ) : ℝ) ≤ ((6665682200217 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2744 : ((155395 / 9007199254740992 : ℚ) : ℝ) ≤ logKernel ((343 / 8 : ℚ) : ℝ) ∧
    logKernel ((343 / 8 : ℚ) : ℝ) ≤ ((1243165 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2744
  constructor
  · exact (show ((155395 / 9007199254740992 : ℚ) : ℝ) ≤ zKernel ((3332841100107 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((343 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((6665682200217 / 18446744073709551616 : ℚ) : ℝ) ≤ ((1243165 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2745 : ((6562340376321 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2745 / 64 : ℚ) : ℝ) ∧
    heightZ ((2745 / 64 : ℚ) : ℝ) ≤ ((1640585094081 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((6562340376321 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2745 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2507 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2745 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2507 / 192 : ℚ) : ℝ) ≤ ((1640585094081 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2745 : ((75307 / 4503599627370496 : ℚ) : ℝ) ≤ logKernel ((2745 / 64 : ℚ) : ℝ) ∧
    logKernel ((2745 / 64 : ℚ) : ℝ) ≤ ((1204917 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2745
  constructor
  · exact (show ((75307 / 4503599627370496 : ℚ) : ℝ) ≤ zKernel ((6562340376321 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2745 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1640585094081 / 4611686018427387904 : ℚ) : ℝ) ≤ ((1204917 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2746 : ((6460600718905 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1373 / 32 : ℚ) : ℝ) ∧
    heightZ ((1373 / 32 : ℚ) : ℝ) ≤ ((1615150179727 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((6460600718905 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1373 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1255 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1373 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1255 / 96 : ℚ) : ℝ) ≤ ((1615150179727 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2746 : ((36495 / 2251799813685248 : ℚ) : ℝ) ≤ logKernel ((1373 / 32 : ℚ) : ℝ) ∧
    logKernel ((1373 / 32 : ℚ) : ℝ) ≤ ((1167845 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2746
  constructor
  · exact (show ((36495 / 2251799813685248 : ℚ) : ℝ) ≤ zKernel ((6460600718905 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1373 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1615150179727 / 4611686018427387904 : ℚ) : ℝ) ≤ ((1167845 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2747 : ((1590109597169 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((2747 / 64 : ℚ) : ℝ) ∧
    heightZ ((2747 / 64 : ℚ) : ℝ) ≤ ((6360438388679 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((1590109597169 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((2747 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2513 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2747 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2513 / 192 : ℚ) : ℝ) ≤ ((6360438388679 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2747 : ((565955 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2747 / 64 : ℚ) : ℝ) ∧
    logKernel ((2747 / 64 : ℚ) : ℝ) ≤ ((1131915 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2747
  constructor
  · exact (show ((565955 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((1590109597169 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2747 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((6360438388679 / 18446744073709551616 : ℚ) : ℝ) ≤ ((1131915 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2748 : ((1565457232861 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((687 / 16 : ℚ) : ℝ) ∧
    heightZ ((687 / 16 : ℚ) : ℝ) ≤ ((6261828931447 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((1565457232861 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((687 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-629 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((687 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-629 / 48 : ℚ) : ℝ) ≤ ((6261828931447 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2748 : ((274271 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((687 / 16 : ℚ) : ℝ) ∧
    logKernel ((687 / 16 : ℚ) : ℝ) ≤ ((1097089 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2748
  constructor
  · exact (show ((274271 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((1565457232861 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((687 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((6261828931447 / 18446744073709551616 : ℚ) : ℝ) ≤ ((1097089 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2749 : ((385296767009 / 1152921504606846976 : ℚ) : ℝ) ≤ heightZ ((2749 / 64 : ℚ) : ℝ) ∧
    heightZ ((2749 / 64 : ℚ) : ℝ) ≤ ((6164748272147 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((385296767009 / 1152921504606846976 : ℚ) : ℝ) ≤ Real.exp (-((2749 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2519 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2749 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2519 / 192 : ℚ) : ℝ) ≤ ((6164748272147 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2749 : ((531665 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2749 / 64 : ℚ) : ℝ) ∧
    logKernel ((2749 / 64 : ℚ) : ℝ) ≤ ((1063335 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2749
  constructor
  · exact (show ((531665 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((385296767009 / 1152921504606846976 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2749 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((6164748272147 / 18446744073709551616 : ℚ) : ℝ) ≤ ((1063335 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2750 : ((6069172708961 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1375 / 32 : ℚ) : ℝ) ∧
    heightZ ((1375 / 32 : ℚ) : ℝ) ≤ ((1517293177241 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((6069172708961 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1375 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1261 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1375 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1261 / 96 : ℚ) : ℝ) ≤ ((1517293177241 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2750 : ((1030615 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1375 / 32 : ℚ) : ℝ) ∧
    logKernel ((1375 / 32 : ℚ) : ℝ) ≤ ((257655 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2750
  constructor
  · exact (show ((1030615 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((6069172708961 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1375 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1517293177241 / 4611686018427387904 : ℚ) : ℝ) ≤ ((257655 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2751 : ((5975078907543 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2751 / 64 : ℚ) : ℝ) ∧
    heightZ ((2751 / 64 : ℚ) : ℝ) ≤ ((2987539453773 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((5975078907543 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2751 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2525 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2751 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2525 / 192 : ℚ) : ℝ) ≤ ((2987539453773 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2751 : ((499453 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2751 / 64 : ℚ) : ℝ) ∧
    logKernel ((2751 / 64 : ℚ) : ℝ) ≤ ((998911 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2751
  constructor
  · exact (show ((499453 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((5975078907543 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2751 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((2987539453773 / 9223372036854775808 : ℚ) : ℝ) ≤ ((998911 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2752 : ((2941221947651 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((43 / 1 : ℚ) : ℝ) ∧
    heightZ ((43 / 1 : ℚ) : ℝ) ≤ ((5882443895305 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((2941221947651 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((43 / 1 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-79 / 6 : ℚ) : ℝ) ∧
      Real.exp (-((43 / 1 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-79 / 6 : ℚ) : ℝ) ≤ ((5882443895305 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2752 : ((968173 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((43 / 1 : ℚ) : ℝ) ∧
    logKernel ((43 / 1 : ℚ) : ℝ) ≤ ((484089 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2752
  constructor
  · exact (show ((968173 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((2941221947651 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((43 / 1 : ℚ) : ℝ)) hh).trans
      (show zKernel ((5882443895305 / 18446744073709551616 : ℚ) : ℝ) ≤ ((484089 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2753 : ((5791245055809 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2753 / 64 : ℚ) : ℝ) ∧
    heightZ ((2753 / 64 : ℚ) : ℝ) ≤ ((1447811263953 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((5791245055809 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2753 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2531 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2753 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2531 / 192 : ℚ) : ℝ) ≤ ((1447811263953 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2753 : ((469193 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2753 / 64 : ℚ) : ℝ) ∧
    logKernel ((2753 / 64 : ℚ) : ℝ) ≤ ((938391 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2753
  constructor
  · exact (show ((469193 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((5791245055809 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2753 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1447811263953 / 4611686018427387904 : ℚ) : ℝ) ≤ ((938391 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2754 : ((5701460123269 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1377 / 32 : ℚ) : ℝ) ∧
    heightZ ((1377 / 32 : ℚ) : ℝ) ≤ ((712682515409 / 2305843009213693952 : ℚ) : ℝ) := by
  have h : ((5701460123269 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1377 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1267 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1377 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1267 / 96 : ℚ) : ℝ) ≤ ((712682515409 / 2305843009213693952 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2754 : ((454757 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((1377 / 32 : ℚ) : ℝ) ∧
    logKernel ((1377 / 32 : ℚ) : ℝ) ≤ ((909519 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2754
  constructor
  · exact (show ((454757 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((5701460123269 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1377 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((712682515409 / 2305843009213693952 : ℚ) : ℝ) ≤ ((909519 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2755 : ((5613067177087 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2755 / 64 : ℚ) : ℝ) ∧
    heightZ ((2755 / 64 : ℚ) : ℝ) ≤ ((2806533588545 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((5613067177087 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2755 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2537 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2755 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2537 / 192 : ℚ) : ℝ) ≤ ((2806533588545 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2755 : ((881531 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2755 / 64 : ℚ) : ℝ) ∧
    logKernel ((2755 / 64 : ℚ) : ℝ) ≤ ((6887 / 562949953421312 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2755
  constructor
  · exact (show ((881531 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((5613067177087 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2755 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((2806533588545 / 9223372036854775808 : ℚ) : ℝ) ≤ ((6887 / 562949953421312 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2756 : ((2763022318257 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((689 / 16 : ℚ) : ℝ) ∧
    heightZ ((689 / 16 : ℚ) : ℝ) ≤ ((5526044636517 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((2763022318257 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((689 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-635 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((689 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-635 / 48 : ℚ) : ℝ) ≤ ((5526044636517 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2756 : ((427205 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((689 / 16 : ℚ) : ℝ) ∧
    logKernel ((689 / 16 : ℚ) : ℝ) ≤ ((854415 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2756
  constructor
  · exact (show ((427205 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((2763022318257 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((689 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((5526044636517 / 18446744073709551616 : ℚ) : ℝ) ≤ ((854415 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2757 : ((5440371255381 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2757 / 64 : ℚ) : ℝ) ∧
    heightZ ((2757 / 64 : ℚ) : ℝ) ≤ ((680046406923 / 2305843009213693952 : ℚ) : ℝ) := by
  have h : ((5440371255381 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2757 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2543 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2757 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2543 / 192 : ℚ) : ℝ) ≤ ((680046406923 / 2305843009213693952 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2757 : ((414061 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2757 / 64 : ℚ) : ℝ) ∧
    logKernel ((2757 / 64 : ℚ) : ℝ) ≤ ((828127 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2757
  constructor
  · exact (show ((414061 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((5440371255381 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2757 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((680046406923 / 2305843009213693952 : ℚ) : ℝ) ≤ ((828127 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2758 : ((5356026116909 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1379 / 32 : ℚ) : ℝ) ∧
    heightZ ((1379 / 32 : ℚ) : ℝ) ≤ ((334751632307 / 1152921504606846976 : ℚ) : ℝ) := by
  have h : ((5356026116909 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1379 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1273 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1379 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1273 / 96 : ℚ) : ℝ) ≤ ((334751632307 / 1152921504606846976 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2758 : ((802643 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1379 / 32 : ℚ) : ℝ) ∧
    logKernel ((1379 / 32 : ℚ) : ℝ) ≤ ((100331 / 9007199254740992 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2758
  constructor
  · exact (show ((802643 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((5356026116909 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1379 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((334751632307 / 1152921504606846976 : ℚ) : ℝ) ≤ ((100331 / 9007199254740992 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2759 : ((5272988628605 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2759 / 64 : ℚ) : ℝ) ∧
    heightZ ((2759 / 64 : ℚ) : ℝ) ≤ ((41195223661 / 144115188075855872 : ℚ) : ℝ) := by
  have h : ((5272988628605 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2759 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2549 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2759 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2549 / 192 : ℚ) : ℝ) ≤ ((41195223661 / 144115188075855872 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2759 : ((194487 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((2759 / 64 : ℚ) : ℝ) ∧
    logKernel ((2759 / 64 : ℚ) : ℝ) ≤ ((777953 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2759
  constructor
  · exact (show ((194487 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((5272988628605 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2759 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((41195223661 / 144115188075855872 : ℚ) : ℝ) ≤ ((777953 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2760 : ((5191238517231 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((345 / 8 : ℚ) : ℝ) ∧
    heightZ ((345 / 8 : ℚ) : ℝ) ≤ ((2595619258617 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((5191238517231 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((345 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-319 / 24 : ℚ) : ℝ) ∧
      Real.exp (-((345 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-319 / 24 : ℚ) : ℝ) ≤ ((2595619258617 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2760 : ((754013 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((345 / 8 : ℚ) : ℝ) ∧
    logKernel ((345 / 8 : ℚ) : ℝ) ≤ ((377009 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2760
  constructor
  · exact (show ((754013 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((5191238517231 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((345 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((2595619258617 / 9223372036854775808 : ℚ) : ℝ) ≤ ((377009 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2761 : ((5110755823859 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2761 / 64 : ℚ) : ℝ) ∧
    heightZ ((2761 / 64 : ℚ) : ℝ) ≤ ((2555377911931 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((5110755823859 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2761 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2555 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2761 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2555 / 192 : ℚ) : ℝ) ≤ ((2555377911931 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2761 : ((730815 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2761 / 64 : ℚ) : ℝ) ∧
    logKernel ((2761 / 64 : ℚ) : ℝ) ≤ ((182705 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2761
  constructor
  · exact (show ((730815 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((5110755823859 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2761 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((2555377911931 / 9223372036854775808 : ℚ) : ℝ) ≤ ((182705 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2762 : ((2515760449497 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((1381 / 32 : ℚ) : ℝ) ∧
    heightZ ((1381 / 32 : ℚ) : ℝ) ≤ ((5031520898997 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((2515760449497 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((1381 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1279 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1381 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1279 / 96 : ℚ) : ℝ) ≤ ((5031520898997 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2762 : ((354165 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((1381 / 32 : ℚ) : ℝ) ∧
    logKernel ((1381 / 32 : ℚ) : ℝ) ≤ ((708335 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2762
  constructor
  · exact (show ((354165 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((2515760449497 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1381 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((5031520898997 / 18446744073709551616 : ℚ) : ℝ) ≤ ((708335 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2763 : ((2476757198889 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2763 / 64 : ℚ) : ℝ) ∧
    heightZ ((2763 / 64 : ℚ) : ℝ) ≤ ((4953514397781 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((2476757198889 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2763 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2561 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2763 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2561 / 192 : ℚ) : ℝ) ≤ ((4953514397781 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2763 : ((686537 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2763 / 64 : ℚ) : ℝ) ∧
    logKernel ((2763 / 64 : ℚ) : ℝ) ≤ ((343271 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2763
  constructor
  · exact (show ((686537 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((2476757198889 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2763 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((4953514397781 / 18446744073709551616 : ℚ) : ℝ) ≤ ((343271 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2764 : ((4876717275267 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((691 / 16 : ℚ) : ℝ) ∧
    heightZ ((691 / 16 : ℚ) : ℝ) ≤ ((2438358637635 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((4876717275267 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((691 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-641 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((691 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-641 / 48 : ℚ) : ℝ) ≤ ((2438358637635 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2764 : ((332707 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((691 / 16 : ℚ) : ℝ) ∧
    logKernel ((691 / 16 : ℚ) : ℝ) ≤ ((665419 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2764
  constructor
  · exact (show ((332707 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((4876717275267 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((691 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((2438358637635 / 9223372036854775808 : ℚ) : ℝ) ≤ ((665419 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2765 : ((600138847723 / 2305843009213693952 : ℚ) : ℝ) ≤ heightZ ((2765 / 64 : ℚ) : ℝ) ∧
    heightZ ((2765 / 64 : ℚ) : ℝ) ≤ ((4801110781787 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((600138847723 / 2305843009213693952 : ℚ) : ℝ) ≤ Real.exp (-((2765 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2567 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2765 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2567 / 192 : ℚ) : ℝ) ≤ ((4801110781787 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2765 : ((322471 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2765 / 64 : ℚ) : ℝ) ∧
    logKernel ((2765 / 64 : ℚ) : ℝ) ≤ ((644947 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2765
  constructor
  · exact (show ((322471 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((600138847723 / 2305843009213693952 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2765 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((4801110781787 / 18446744073709551616 : ℚ) : ℝ) ≤ ((644947 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2766 : ((2363338229167 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((1383 / 32 : ℚ) : ℝ) ∧
    heightZ ((1383 / 32 : ℚ) : ℝ) ≤ ((4726676458337 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((2363338229167 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((1383 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1285 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1383 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1285 / 96 : ℚ) : ℝ) ≤ ((4726676458337 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2766 : ((625099 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1383 / 32 : ℚ) : ℝ) ∧
    logKernel ((1383 / 32 : ℚ) : ℝ) ≤ ((39069 / 4503599627370496 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2766
  constructor
  · exact (show ((625099 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((2363338229167 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1383 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((4726676458337 / 18446744073709551616 : ℚ) : ℝ) ≤ ((39069 / 4503599627370496 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2767 : ((4653396132107 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2767 / 64 : ℚ) : ℝ) ∧
    heightZ ((2767 / 64 : ℚ) : ℝ) ≤ ((2326698066055 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((4653396132107 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2767 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2573 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2767 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2573 / 192 : ℚ) : ℝ) ≤ ((2326698066055 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2767 : ((302933 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2767 / 64 : ℚ) : ℝ) ∧
    logKernel ((2767 / 64 : ℚ) : ℝ) ≤ ((605871 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2767
  constructor
  · exact (show ((302933 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((4653396132107 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2767 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((2326698066055 / 9223372036854775808 : ℚ) : ℝ) ≤ ((605871 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2768 : ((2290625956017 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((173 / 4 : ℚ) : ℝ) ∧
    heightZ ((173 / 4 : ℚ) : ℝ) ≤ ((4581251912037 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((2290625956017 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((173 / 4 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-161 / 12 : ℚ) : ℝ) ∧
      Real.exp (-((173 / 4 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-161 / 12 : ℚ) : ℝ) ≤ ((4581251912037 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2768 : ((293613 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((173 / 4 : ℚ) : ℝ) ∧
    logKernel ((173 / 4 : ℚ) : ℝ) ≤ ((587231 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2768
  constructor
  · exact (show ((293613 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((2290625956017 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((173 / 4 : ℚ) : ℝ)) hh).trans
      (show zKernel ((4581251912037 / 18446744073709551616 : ℚ) : ℝ) ≤ ((587231 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2769 : ((2255113092211 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2769 / 64 : ℚ) : ℝ) ∧
    heightZ ((2769 / 64 : ℚ) : ℝ) ≤ ((4510226184425 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((2255113092211 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2769 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2579 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2769 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2579 / 192 : ℚ) : ℝ) ≤ ((4510226184425 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2769 : ((569159 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2769 / 64 : ℚ) : ℝ) ∧
    logKernel ((2769 / 64 : ℚ) : ℝ) ≤ ((142291 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2769
  constructor
  · exact (show ((569159 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((2255113092211 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2769 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((4510226184425 / 18446744073709551616 : ℚ) : ℝ) ≤ ((142291 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem log_height_bounds_896 : ((67663880845146235 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((1369 / 32 : ℚ) : ℝ) ∧
    Real.log ((1369 / 32 : ℚ) : ℝ) ≤ ((270655523380584943 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((67663880845146235 / 18014398509481984 : ℚ) : ℝ) ≤ ((1369 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1369 / 32 : ℚ) : ℝ) ≤ Real.exp ((270655523380584943 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_896 : heightPower (896 : Fin 988) ≤ ((4052317812267235 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_896
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_896 : heightFactor (896 : Fin 988) ≤ ((82678443 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_896
  obtain ⟨hpl, hph⟩ := kernel_bounds_2737
  obtain ⟨hcl, hch⟩ := kernel_bounds_2738
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2738
  have h : (((1874161 / 512 : ℚ) : ℝ) * (logKernel ((2737 / 64 : ℚ) : ℝ) - logKernel ((1369 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1369 / 32 : ℚ) : ℝ) + Real.log ((1369 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((82678443 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_897 : ((67670459044419435 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((2739 / 64 : ℚ) : ℝ) ∧
    Real.log ((2739 / 64 : ℚ) : ℝ) ≤ ((270681836177677743 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((67670459044419435 / 18014398509481984 : ℚ) : ℝ) ≤ ((2739 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2739 / 64 : ℚ) : ℝ) ≤ Real.exp ((270681836177677743 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_897 : heightPower (897 : Fin 988) ≤ ((4056818643141983 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_897
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_897 : heightFactor (897 : Fin 988) ≤ ((40311723 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_897
  obtain ⟨hpl, hph⟩ := kernel_bounds_2738
  obtain ⟨hcl, hch⟩ := kernel_bounds_2739
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2739
  have h : (((7502121 / 2048 : ℚ) : ℝ) * (logKernel ((1369 / 32 : ℚ) : ℝ) - logKernel ((2739 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2739 / 64 : ℚ) : ℝ) + Real.log ((2739 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((40311723 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_898 : ((270708139369806979 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((685 / 16 : ℚ) : ℝ) ∧
    Real.log ((685 / 16 : ℚ) : ℝ) ≤ ((135354069684903491 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((270708139369806979 / 72057594037927936 : ℚ) : ℝ) ≤ ((685 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((685 / 16 : ℚ) : ℝ) ≤ Real.exp ((135354069684903491 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_898 : heightPower (898 : Fin 988) ≤ ((2030659718248671 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_898
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_898 : heightFactor (898 : Fin 988) ≤ ((78619543 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_898
  obtain ⟨hpl, hph⟩ := kernel_bounds_2739
  obtain ⟨hcl, hch⟩ := kernel_bounds_2740
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2740
  have h : (((469225 / 128 : ℚ) : ℝ) * (logKernel ((2739 / 64 : ℚ) : ℝ) - logKernel ((685 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((685 / 16 : ℚ) : ℝ) + Real.log ((685 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((78619543 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_899 : ((67683608240995575 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((2741 / 64 : ℚ) : ℝ) ∧
    Real.log ((2741 / 64 : ℚ) : ℝ) ≤ ((270734432963982303 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((67683608240995575 / 18014398509481984 : ℚ) : ℝ) ≤ ((2741 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2741 / 64 : ℚ) : ℝ) ≤ Real.exp ((270734432963982303 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_899 : heightPower (899 : Fin 988) ≤ ((4065820192360693 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_899
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_899 : heightFactor (899 : Fin 988) ≤ ((9583183 / 35184372088832 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_899
  obtain ⟨hpl, hph⟩ := kernel_bounds_2740
  obtain ⟨hcl, hch⟩ := kernel_bounds_2741
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2741
  have h : (((7513081 / 2048 : ℚ) : ℝ) * (logKernel ((685 / 16 : ℚ) : ℝ) - logKernel ((2741 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2741 / 64 : ℚ) : ℝ) + Real.log ((2741 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((9583183 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_900 : ((135380358483602837 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((1371 / 32 : ℚ) : ℝ) ∧
    Real.log ((1371 / 32 : ℚ) : ℝ) ≤ ((270760716967205677 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((135380358483602837 / 36028797018963968 : ℚ) : ℝ) ≤ ((1371 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1371 / 32 : ℚ) : ℝ) ≤ Real.exp ((270760716967205677 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_900 : heightPower (900 : Fin 988) ≤ ((4070320910759389 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_900
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_900 : heightFactor (900 : Fin 988) ≤ ((74759971 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_900
  obtain ⟨hpl, hph⟩ := kernel_bounds_2741
  obtain ⟨hcl, hch⟩ := kernel_bounds_2742
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2742
  have h : (((1879641 / 512 : ℚ) : ℝ) * (logKernel ((2741 / 64 : ℚ) : ℝ) - logKernel ((1371 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1371 / 32 : ℚ) : ℝ) + Real.log ((1371 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((74759971 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_901 : ((270786991386471417 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2743 / 64 : ℚ) : ℝ) ∧
    Real.log ((2743 / 64 : ℚ) : ℝ) ≤ ((67696747846617855 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((270786991386471417 / 72057594037927936 : ℚ) : ℝ) ≤ ((2743 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2743 / 64 : ℚ) : ℝ) ≤ Real.exp ((67696747846617855 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_901 : heightPower (901 : Fin 988) ≤ ((4074821591720749 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_901
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_901 : heightFactor (901 : Fin 988) ≤ ((72901855 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_901
  obtain ⟨hpl, hph⟩ := kernel_bounds_2742
  obtain ⟨hcl, hch⟩ := kernel_bounds_2743
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2743
  have h : (((7524049 / 2048 : ℚ) : ℝ) * (logKernel ((1371 / 32 : ℚ) : ℝ) - logKernel ((2743 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2743 / 64 : ℚ) : ℝ) + Real.log ((2743 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((72901855 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_902 : ((270813256228766193 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((343 / 8 : ℚ) : ℝ) ∧
    Real.log ((343 / 8 : ℚ) : ℝ) ≤ ((67703314057191549 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((270813256228766193 / 72057594037927936 : ℚ) : ℝ) ≤ ((343 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((343 / 8 : ℚ) : ℝ) ≤ Real.exp ((67703314057191549 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_902 : heightPower (902 : Fin 988) ≤ ((4079322235272067 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_902
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_902 : heightFactor (902 : Fin 988) ≤ ((71089941 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_902
  obtain ⟨hpl, hph⟩ := kernel_bounds_2743
  obtain ⟨hcl, hch⟩ := kernel_bounds_2744
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2744
  have h : (((117649 / 32 : ℚ) : ℝ) * (logKernel ((2743 / 64 : ℚ) : ℝ) - logKernel ((343 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((343 / 8 : ℚ) : ℝ) + Real.log ((343 / 8 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((71089941 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_903 : ((270839511501069031 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2745 / 64 : ℚ) : ℝ) ∧
    Real.log ((2745 / 64 : ℚ) : ℝ) ≤ ((135419755750534517 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((270839511501069031 / 72057594037927936 : ℚ) : ℝ) ≤ ((2745 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2745 / 64 : ℚ) : ℝ) ≤ Real.exp ((135419755750534517 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_903 : heightPower (903 : Fin 988) ≤ ((1020955710360151 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_903
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_903 : heightFactor (903 : Fin 988) ≤ ((8665385 / 35184372088832 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_903
  obtain ⟨hpl, hph⟩ := kernel_bounds_2744
  obtain ⟨hcl, hch⟩ := kernel_bounds_2745
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2745
  have h : (((7535025 / 2048 : ℚ) : ℝ) * (logKernel ((343 / 8 : ℚ) : ℝ) - logKernel ((2745 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2745 / 64 : ℚ) : ℝ) + Real.log ((2745 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((8665385 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_904 : ((270865757210351331 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1373 / 32 : ℚ) : ℝ) ∧
    Real.log ((1373 / 32 : ℚ) : ℝ) ≤ ((135432878605175667 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((270865757210351331 / 72057594037927936 : ℚ) : ℝ) ≤ ((1373 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1373 / 32 : ℚ) : ℝ) ≤ Real.exp ((135432878605175667 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_904 : heightPower (904 : Fin 988) ≤ ((511040426281699 / 35184372088832 : ℚ) : ℝ) := by
  have hh := log_height_bounds_904
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_904 : heightFactor (904 : Fin 988) ≤ ((67600151 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_904
  obtain ⟨hpl, hph⟩ := kernel_bounds_2745
  obtain ⟨hcl, hch⟩ := kernel_bounds_2746
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2746
  have h : (((1885129 / 512 : ℚ) : ℝ) * (logKernel ((2745 / 64 : ℚ) : ℝ) - logKernel ((1373 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1373 / 32 : ℚ) : ℝ) + Real.log ((1373 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((67600151 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_905 : ((135445996681788441 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2747 / 64 : ℚ) : ℝ) ∧
    Real.log ((2747 / 64 : ℚ) : ℝ) ≤ ((270891993363576885 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((135445996681788441 / 36028797018963968 : ℚ) : ℝ) ≤ ((2747 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2747 / 64 : ℚ) : ℝ) ≤ Real.exp ((270891993363576885 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_905 : heightPower (905 : Fin 988) ≤ ((2046411970869117 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_905
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_905 : heightFactor (905 : Fin 988) ≤ ((1030001 / 4398046511104 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_905
  obtain ⟨hpl, hph⟩ := kernel_bounds_2746
  obtain ⟨hcl, hch⟩ := kernel_bounds_2747
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2747
  have h : (((7546009 / 2048 : ℚ) : ℝ) * (logKernel ((1373 / 32 : ℚ) : ℝ) - logKernel ((2747 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2747 / 64 : ℚ) : ℝ) + Real.log ((2747 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1030001 / 4398046511104 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_906 : ((270918219967701867 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((687 / 16 : ℚ) : ℝ) ∧
    Real.log ((687 / 16 : ℚ) : ℝ) ≤ ((135459109983850935 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((270918219967701867 / 72057594037927936 : ℚ) : ℝ) ≤ ((687 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((687 / 16 : ℚ) : ℝ) ≤ Real.exp ((135459109983850935 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_906 : heightPower (906 : Fin 988) ≤ ((4097324435921701 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_906
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_906 : heightFactor (906 : Fin 988) ≤ ((8035219 / 35184372088832 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_906
  obtain ⟨hpl, hph⟩ := kernel_bounds_2747
  obtain ⟨hcl, hch⟩ := kernel_bounds_2748
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2748
  have h : (((471969 / 128 : ℚ) : ℝ) * (logKernel ((2747 / 64 : ℚ) : ℝ) - logKernel ((687 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((687 / 16 : ℚ) : ℝ) + Real.log ((687 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((8035219 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_907 : ((270944437029674877 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2749 / 64 : ℚ) : ℝ) ∧
    Real.log ((2749 / 64 : ℚ) : ℝ) ≤ ((2116753414294335 / 562949953421312 : ℚ) : ℝ) := by
  have hl : Real.exp ((270944437029674877 / 72057594037927936 : ℚ) : ℝ) ≤ ((2749 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2749 / 64 : ℚ) : ℝ) ≤ Real.exp ((2116753414294335 / 562949953421312 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_907 : heightPower (907 : Fin 988) ≤ ((4101824892831137 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_907
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_907 : heightFactor (907 : Fin 988) ≤ ((62684179 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_907
  obtain ⟨hpl, hph⟩ := kernel_bounds_2748
  obtain ⟨hcl, hch⟩ := kernel_bounds_2749
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2749
  have h : (((7557001 / 2048 : ℚ) : ℝ) * (logKernel ((687 / 16 : ℚ) : ℝ) - logKernel ((2749 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2749 / 64 : ℚ) : ℝ) + Real.log ((2749 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((62684179 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_908 : ((270970644556436921 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1375 / 32 : ℚ) : ℝ) ∧
    Real.log ((1375 / 32 : ℚ) : ℝ) ≤ ((67742661139109231 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((270970644556436921 / 72057594037927936 : ℚ) : ℝ) ≤ ((1375 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1375 / 32 : ℚ) : ℝ) ≤ Real.exp ((67742661139109231 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_908 : heightPower (908 : Fin 988) ≤ ((4106325312493655 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_908
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_908 : heightFactor (908 : Fin 988) ≤ ((15281583 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_908
  obtain ⟨hpl, hph⟩ := kernel_bounds_2749
  obtain ⟨hcl, hch⟩ := kernel_bounds_2750
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2750
  have h : (((1890625 / 512 : ℚ) : ℝ) * (logKernel ((2749 / 64 : ℚ) : ℝ) - logKernel ((1375 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1375 / 32 : ℚ) : ℝ) + Real.log ((1375 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((15281583 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_909 : ((135498421277460719 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2751 / 64 : ℚ) : ℝ) ∧
    Real.log ((2751 / 64 : ℚ) : ℝ) ≤ ((270996842554921441 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((135498421277460719 / 36028797018963968 : ℚ) : ℝ) ≤ ((2751 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2751 / 64 : ℚ) : ℝ) ≤ Real.exp ((270996842554921441 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_909 : heightPower (909 : Fin 988) ≤ ((4110825694936339 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_909
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_909 : heightFactor (909 : Fin 988) ≤ ((59607223 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_909
  obtain ⟨hpl, hph⟩ := kernel_bounds_2750
  obtain ⟨hcl, hch⟩ := kernel_bounds_2751
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2751
  have h : (((7568001 / 2048 : ℚ) : ℝ) * (logKernel ((1375 / 32 : ℚ) : ℝ) - logKernel ((2751 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2751 / 64 : ℚ) : ℝ) + Real.log ((2751 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((59607223 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_910 : ((271023031032054305 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((43 / 1 : ℚ) : ℝ) ∧
    Real.log ((43 / 1 : ℚ) : ℝ) ≤ ((67755757758013577 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((271023031032054305 / 72057594037927936 : ℚ) : ℝ) ≤ ((43 / 1 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((43 / 1 : ℚ) : ℝ) ≤ Real.exp ((67755757758013577 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_910 : heightPower (910 : Fin 988) ≤ ((1028831510046561 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_910
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_910 : heightFactor (910 : Fin 988) ≤ ((58125889 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_910
  obtain ⟨hpl, hph⟩ := kernel_bounds_2751
  obtain ⟨hcl, hch⟩ := kernel_bounds_2752
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2752
  have h : (((3698 / 1 : ℚ) : ℝ) * (logKernel ((2751 / 64 : ℚ) : ℝ) - logKernel ((43 / 1 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((43 / 1 : ℚ) : ℝ) + Real.log ((43 / 1 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((58125889 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_911 : ((271049209994753855 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2753 / 64 : ℚ) : ℝ) ∧
    Real.log ((2753 / 64 : ℚ) : ℝ) ≤ ((135524604997376929 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((271049209994753855 / 72057594037927936 : ℚ) : ℝ) ≤ ((2753 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2753 / 64 : ℚ) : ℝ) ≤ Real.exp ((135524604997376929 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_911 : heightPower (911 : Fin 988) ≤ ((4119826348270393 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_911
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_911 : heightFactor (911 : Fin 988) ≤ ((3542587 / 17592186044416 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_911
  obtain ⟨hpl, hph⟩ := kernel_bounds_2752
  obtain ⟨hcl, hch⟩ := kernel_bounds_2753
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2753
  have h : (((7579009 / 2048 : ℚ) : ℝ) * (logKernel ((43 / 1 : ℚ) : ℝ) - logKernel ((2753 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2753 / 64 : ℚ) : ℝ) + Real.log ((2753 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((3542587 / 17592186044416 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_912 : ((135537689724965439 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((1377 / 32 : ℚ) : ℝ) ∧
    Real.log ((1377 / 32 : ℚ) : ℝ) ≤ ((271075379449930881 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((135537689724965439 / 36028797018963968 : ℚ) : ℝ) ≤ ((1377 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1377 / 32 : ℚ) : ℝ) ≤ Real.exp ((271075379449930881 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_912 : heightPower (912 : Fin 988) ≤ ((2062163309607891 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_912
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_912 : heightFactor (912 : Fin 988) ≤ ((3454551 / 17592186044416 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_912
  obtain ⟨hpl, hph⟩ := kernel_bounds_2753
  obtain ⟨hcl, hch⟩ := kernel_bounds_2754
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2754
  have h : (((1896129 / 512 : ℚ) : ℝ) * (logKernel ((2753 / 64 : ℚ) : ℝ) - logKernel ((1377 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1377 / 32 : ℚ) : ℝ) + Real.log ((1377 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((3454551 / 17592186044416 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_913 : ((271101539404488641 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2755 / 64 : ℚ) : ℝ) ∧
    Real.log ((2755 / 64 : ℚ) : ℝ) ≤ ((67775384851122161 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((271101539404488641 / 72057594037927936 : ℚ) : ℝ) ≤ ((2755 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2755 / 64 : ℚ) : ℝ) ≤ Real.exp ((67775384851122161 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_913 : heightPower (913 : Fin 988) ≤ ((4128826853049377 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_913
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_913 : heightFactor (913 : Fin 988) ≤ ((13474817 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_913
  obtain ⟨hpl, hph⟩ := kernel_bounds_2754
  obtain ⟨hcl, hch⟩ := kernel_bounds_2755
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2755
  have h : (((7590025 / 2048 : ℚ) : ℝ) * (logKernel ((1377 / 32 : ℚ) : ℝ) - logKernel ((2755 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2755 / 64 : ℚ) : ℝ) + Real.log ((2755 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((13474817 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_914 : ((135563844932661447 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((689 / 16 : ℚ) : ℝ) ∧
    Real.log ((689 / 16 : ℚ) : ℝ) ≤ ((271127689865322897 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((135563844932661447 / 36028797018963968 : ℚ) : ℝ) ≤ ((689 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((689 / 16 : ℚ) : ℝ) ≤ Real.exp ((271127689865322897 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_914 : heightPower (914 : Fin 988) ≤ ((4133327049798115 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_914
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_914 : heightFactor (914 : Fin 988) ≤ ((26279939 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_914
  obtain ⟨hpl, hph⟩ := kernel_bounds_2755
  obtain ⟨hcl, hch⟩ := kernel_bounds_2756
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2756
  have h : (((474721 / 128 : ℚ) : ℝ) * (logKernel ((2755 / 64 : ℚ) : ℝ) - logKernel ((689 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((689 / 16 : ℚ) : ℝ) + Real.log ((689 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((26279939 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_915 : ((135576915419660941 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2757 / 64 : ℚ) : ℝ) ∧
    Real.log ((2757 / 64 : ℚ) : ℝ) ≤ ((271153830839321885 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((135576915419660941 / 36028797018963968 : ℚ) : ℝ) ≤ ((2757 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2757 / 64 : ℚ) : ℝ) ≤ Real.exp ((271153830839321885 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_915 : heightPower (915 : Fin 988) ≤ ((4137827209488903 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_915
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_915 : heightFactor (915 : Fin 988) ≤ ((12813449 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_915
  obtain ⟨hpl, hph⟩ := kernel_bounds_2756
  obtain ⟨hcl, hch⟩ := kernel_bounds_2757
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2757
  have h : (((7601049 / 2048 : ℚ) : ℝ) * (logKernel ((689 / 16 : ℚ) : ℝ) - logKernel ((2757 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2757 / 64 : ℚ) : ℝ) + Real.log ((2757 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((12813449 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_916 : ((271179962333366357 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1379 / 32 : ℚ) : ℝ) ∧
    Real.log ((1379 / 32 : ℚ) : ℝ) ≤ ((33897495291670795 / 9007199254740992 : ℚ) : ℝ) := by
  have hl : Real.exp ((271179962333366357 / 72057594037927936 : ℚ) : ℝ) ≤ ((1379 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1379 / 32 : ℚ) : ℝ) ≤ Real.exp ((33897495291670795 / 9007199254740992 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_916 : heightPower (916 : Fin 988) ≤ ((2071163666074309 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_916
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_916 : heightFactor (916 : Fin 988) ≤ ((49980195 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_916
  obtain ⟨hpl, hph⟩ := kernel_bounds_2757
  obtain ⟨hcl, hch⟩ := kernel_bounds_2758
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2758
  have h : (((1901641 / 512 : ℚ) : ℝ) * (logKernel ((2757 / 64 : ℚ) : ℝ) - logKernel ((1379 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1379 / 32 : ℚ) : ℝ) + Real.log ((1379 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((49980195 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_917 : ((271206084354329585 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2759 / 64 : ℚ) : ℝ) ∧
    Real.log ((2759 / 64 : ℚ) : ℝ) ≤ ((67801521088582397 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((271206084354329585 / 72057594037927936 : ℚ) : ℝ) ≤ ((2759 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2759 / 64 : ℚ) : ℝ) ≤ Real.exp ((67801521088582397 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_917 : heightPower (917 : Fin 988) ≤ ((4146827417804109 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_917
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_917 : heightFactor (917 : Fin 988) ≤ ((24369133 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_917
  obtain ⟨hpl, hph⟩ := kernel_bounds_2758
  obtain ⟨hcl, hch⟩ := kernel_bounds_2759
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2759
  have h : (((7612081 / 2048 : ℚ) : ℝ) * (logKernel ((1379 / 32 : ℚ) : ℝ) - logKernel ((2759 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2759 / 64 : ℚ) : ℝ) + Real.log ((2759 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((24369133 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_918 : ((271232196909077363 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((345 / 8 : ℚ) : ℝ) ∧
    Real.log ((345 / 8 : ℚ) : ℝ) ≤ ((135616098454538683 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((271232196909077363 / 72057594037927936 : ℚ) : ℝ) ≤ ((345 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((345 / 8 : ℚ) : ℝ) ≤ Real.exp ((135616098454538683 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_918 : heightPower (918 : Fin 988) ≤ ((4151327466482197 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_918
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_918 : heightFactor (918 : Fin 988) ≤ ((5940903 / 35184372088832 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_918
  obtain ⟨hpl, hph⟩ := kernel_bounds_2759
  obtain ⟨hcl, hch⟩ := kernel_bounds_2760
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2760
  have h : (((119025 / 32 : ℚ) : ℝ) * (logKernel ((2759 / 64 : ℚ) : ℝ) - logKernel ((345 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((345 / 8 : ℚ) : ℝ) + Real.log ((345 / 8 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((5940903 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_919 : ((271258300004468025 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2761 / 64 : ℚ) : ℝ) ∧
    Real.log ((2761 / 64 : ℚ) : ℝ) ≤ ((67814575001117007 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((271258300004468025 / 72057594037927936 : ℚ) : ℝ) ≤ ((2761 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2761 / 64 : ℚ) : ℝ) ≤ Real.exp ((67814575001117007 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_919 : heightPower (919 : Fin 988) ≤ ((4155827478209671 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_919
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_919 : heightFactor (919 : Fin 988) ≤ ((11586575 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_919
  obtain ⟨hpl, hph⟩ := kernel_bounds_2760
  obtain ⟨hcl, hch⟩ := kernel_bounds_2761
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2761
  have h : (((7623121 / 2048 : ℚ) : ℝ) * (logKernel ((345 / 8 : ℚ) : ℝ) - logKernel ((2761 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2761 / 64 : ℚ) : ℝ) + Real.log ((2761 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((11586575 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_920 : ((135642196823676227 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((1381 / 32 : ℚ) : ℝ) ∧
    Real.log ((1381 / 32 : ℚ) : ℝ) ≤ ((271284393647352457 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((135642196823676227 / 36028797018963968 : ℚ) : ℝ) ≤ ((1381 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1381 / 32 : ℚ) : ℝ) ≤ Real.exp ((271284393647352457 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_920 : heightPower (920 : Fin 988) ≤ ((1040081863253323 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_920
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_920 : heightFactor (920 : Fin 988) ≤ ((45194745 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_920
  obtain ⟨hpl, hph⟩ := kernel_bounds_2761
  obtain ⟨hcl, hch⟩ := kernel_bounds_2762
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2762
  have h : (((1907161 / 512 : ℚ) : ℝ) * (logKernel ((2761 / 64 : ℚ) : ℝ) - logKernel ((1381 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1381 / 32 : ℚ) : ℝ) + Real.log ((1381 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((45194745 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_921 : ((135655238922287047 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2763 / 64 : ℚ) : ℝ) ∧
    Real.log ((2763 / 64 : ℚ) : ℝ) ≤ ((271310477844574097 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((135655238922287047 / 36028797018963968 : ℚ) : ℝ) ≤ ((2763 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2763 / 64 : ℚ) : ℝ) ≤ Real.exp ((271310477844574097 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_921 : heightPower (921 : Fin 988) ≤ ((4164827390919793 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_921
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_921 : heightFactor (921 : Fin 988) ≤ ((22035915 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_921
  obtain ⟨hpl, hph⟩ := kernel_bounds_2762
  obtain ⟨hcl, hch⟩ := kernel_bounds_2763
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2763
  have h : (((7634169 / 2048 : ℚ) : ℝ) * (logKernel ((1381 / 32 : ℚ) : ℝ) - logKernel ((2763 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2763 / 64 : ℚ) : ℝ) + Real.log ((2763 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((22035915 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_922 : ((2119816817210695 / 562949953421312 : ℚ) : ℝ) ≤ Real.log ((691 / 16 : ℚ) : ℝ) ∧
    Real.log ((691 / 16 : ℚ) : ℝ) ≤ ((271336552602968963 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((2119816817210695 / 562949953421312 : ℚ) : ℝ) ≤ ((691 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((691 / 16 : ℚ) : ℝ) ≤ Real.exp ((271336552602968963 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_922 : heightPower (922 : Fin 988) ≤ ((4169327291955877 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_922
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_922 : heightFactor (922 : Fin 988) ≤ ((42976843 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_922
  obtain ⟨hpl, hph⟩ := kernel_bounds_2763
  obtain ⟨hcl, hch⟩ := kernel_bounds_2764
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2764
  have h : (((477481 / 128 : ℚ) : ℝ) * (logKernel ((2763 / 64 : ℚ) : ℝ) - logKernel ((691 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((691 / 16 : ℚ) : ℝ) + Real.log ((691 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((42976843 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_923 : ((16960163620585353 / 4503599627370496 : ℚ) : ℝ) ≤ Real.log ((2765 / 64 : ℚ) : ℝ) ∧
    Real.log ((2765 / 64 : ℚ) : ℝ) ≤ ((271362617929365651 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((16960163620585353 / 4503599627370496 : ℚ) : ℝ) ≤ ((2765 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2765 / 64 : ℚ) : ℝ) ≤ Real.exp ((271362617929365651 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_923 : heightPower (923 : Fin 988) ≤ ((2086913578074109 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_923
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_923 : heightFactor (923 : Fin 988) ≤ ((1309659 / 8796093022208 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_923
  obtain ⟨hpl, hph⟩ := kernel_bounds_2764
  obtain ⟨hcl, hch⟩ := kernel_bounds_2765
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2765
  have h : (((7645225 / 2048 : ℚ) : ℝ) * (logKernel ((691 / 16 : ℚ) : ℝ) - logKernel ((2765 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2765 / 64 : ℚ) : ℝ) + Real.log ((2765 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1309659 / 8796093022208 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_924 : ((135694336915292673 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((1383 / 32 : ℚ) : ℝ) ∧
    Real.log ((1383 / 32 : ℚ) : ℝ) ≤ ((271388673830585349 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((135694336915292673 / 36028797018963968 : ℚ) : ℝ) ≤ ((1383 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1383 / 32 : ℚ) : ℝ) ≤ Real.exp ((271388673830585349 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_924 : heightPower (924 : Fin 988) ≤ ((2089163491761731 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_924
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_924 : heightFactor (924 : Fin 988) ≤ ((20433945 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_924
  obtain ⟨hpl, hph⟩ := kernel_bounds_2765
  obtain ⟨hcl, hch⟩ := kernel_bounds_2766
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2766
  have h : (((1912689 / 512 : ℚ) : ℝ) * (logKernel ((2765 / 64 : ℚ) : ℝ) - logKernel ((1383 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1383 / 32 : ℚ) : ℝ) + Real.log ((1383 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((20433945 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_925 : ((271414720313441847 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2767 / 64 : ℚ) : ℝ) ∧
    Real.log ((2767 / 64 : ℚ) : ℝ) ≤ ((135707360156720925 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((271414720313441847 / 72057594037927936 : ℚ) : ℝ) ≤ ((2767 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2767 / 64 : ℚ) : ℝ) ≤ Real.exp ((135707360156720925 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_925 : heightPower (925 : Fin 988) ≤ ((65356668345441 / 4398046511104 : ℚ) : ℝ) := by
  have hh := log_height_bounds_925
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_925 : heightFactor (925 : Fin 988) ≤ ((9963147 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_925
  obtain ⟨hpl, hph⟩ := kernel_bounds_2766
  obtain ⟨hcl, hch⟩ := kernel_bounds_2767
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2767
  have h : (((7656289 / 2048 : ℚ) : ℝ) * (logKernel ((1383 / 32 : ℚ) : ℝ) - logKernel ((2767 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2767 / 64 : ℚ) : ℝ) + Real.log ((2767 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((9963147 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_926 : ((135720378692370777 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((173 / 4 : ℚ) : ℝ) ∧
    Real.log ((173 / 4 : ℚ) : ℝ) ≤ ((271440757384741557 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((135720378692370777 / 36028797018963968 : ℚ) : ℝ) ≤ ((173 / 4 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((173 / 4 : ℚ) : ℝ) ≤ Real.exp ((271440757384741557 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_926 : heightPower (926 : Fin 988) ≤ ((1046831631982273 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_926
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_926 : heightFactor (926 : Fin 988) ≤ ((38862539 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_926
  obtain ⟨hpl, hph⟩ := kernel_bounds_2767
  obtain ⟨hcl, hch⟩ := kernel_bounds_2768
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2768
  have h : (((29929 / 8 : ℚ) : ℝ) * (logKernel ((2767 / 64 : ℚ) : ℝ) - logKernel ((173 / 4 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((173 / 4 : ℚ) : ℝ) + Real.log ((173 / 4 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((38862539 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_927 : ((271466785051283499 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2769 / 64 : ℚ) : ℝ) ∧
    Real.log ((2769 / 64 : ℚ) : ℝ) ≤ ((135733392525641751 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((271466785051283499 / 72057594037927936 : ℚ) : ℝ) ≤ ((2769 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2769 / 64 : ℚ) : ℝ) ≤ Real.exp ((135733392525641751 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_927 : heightPower (927 : Fin 988) ≤ ((2095913122506313 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_927
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_927 : heightFactor (927 : Fin 988) ≤ ((18948557 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_927
  obtain ⟨hpl, hph⟩ := kernel_bounds_2768
  obtain ⟨hcl, hch⟩ := kernel_bounds_2769
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2769
  have h : (((7667361 / 2048 : ℚ) : ℝ) * (logKernel ((173 / 4 : ℚ) : ℝ) - logKernel ((2769 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2769 / 64 : ℚ) : ℝ) + Real.log ((2769 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((18948557 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

end LegendreK6.M2Pilot.Enclosures.Height028
