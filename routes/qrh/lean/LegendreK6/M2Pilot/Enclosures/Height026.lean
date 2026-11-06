import LegendreK6.M2PilotDefinitions
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp

/-! Generated proposals: every bound is checked by Lean, not by trusting Arb. -/
namespace LegendreK6.M2Pilot.Enclosures.Height026
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem height_z_bounds_2673 : ((10106715697741 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2673 / 64 : ℚ) : ℝ) ∧
    heightZ ((2673 / 64 : ℚ) : ℝ) ≤ ((20213431395485 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((10106715697741 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2673 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2291 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2673 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2291 / 192 : ℚ) : ℝ) ≤ ((20213431395485 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2673 : ((357247 / 2251799813685248 : ℚ) : ℝ) ≤ logKernel ((2673 / 64 : ℚ) : ℝ) ∧
    logKernel ((2673 / 64 : ℚ) : ℝ) ≤ ((11431909 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2673
  constructor
  · exact (show ((357247 / 2251799813685248 : ℚ) : ℝ) ≤ zKernel ((10106715697741 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2673 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((20213431395485 / 18446744073709551616 : ℚ) : ℝ) ≤ ((11431909 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2674 : ((19900051188505 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1337 / 32 : ℚ) : ℝ) ∧
    heightZ ((1337 / 32 : ℚ) : ℝ) ≤ ((4975012797127 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((19900051188505 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1337 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1147 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1337 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1147 / 96 : ℚ) : ℝ) ≤ ((4975012797127 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2674 : ((11080181 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1337 / 32 : ℚ) : ℝ) ∧
    logKernel ((1337 / 32 : ℚ) : ℝ) ≤ ((5540093 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2674
  constructor
  · exact (show ((11080181 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((19900051188505 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1337 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((4975012797127 / 4611686018427387904 : ℚ) : ℝ) ≤ ((5540093 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2675 : ((4897882372827 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((2675 / 64 : ℚ) : ℝ) ∧
    heightZ ((2675 / 64 : ℚ) : ℝ) ≤ ((19591529491311 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((4897882372827 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((2675 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2297 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2675 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2297 / 192 : ℚ) : ℝ) ≤ ((19591529491311 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2675 : ((671205 / 4503599627370496 : ℚ) : ℝ) ≤ logKernel ((2675 / 64 : ℚ) : ℝ) ∧
    logKernel ((2675 / 64 : ℚ) : ℝ) ≤ ((10739285 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2675
  constructor
  · exact (show ((671205 / 4503599627370496 : ℚ) : ℝ) ≤ zKernel ((4897882372827 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2675 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((19591529491311 / 18446744073709551616 : ℚ) : ℝ) ≤ ((10739285 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2676 : ((19287790979679 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((669 / 16 : ℚ) : ℝ) ∧
    heightZ ((669 / 16 : ℚ) : ℝ) ≤ ((9643895489841 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((19287790979679 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((669 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-575 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((669 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-575 / 48 : ℚ) : ℝ) ≤ ((9643895489841 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2676 : ((10408867 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((669 / 16 : ℚ) : ℝ) ∧
    logKernel ((669 / 16 : ℚ) : ℝ) ≤ ((1301109 / 9007199254740992 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2676
  constructor
  · exact (show ((10408867 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((19287790979679 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((669 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((9643895489841 / 9223372036854775808 : ℚ) : ℝ) ≤ ((1301109 / 9007199254740992 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2677 : ((18988761497199 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2677 / 64 : ℚ) : ℝ) ∧
    heightZ ((2677 / 64 : ℚ) : ℝ) ≤ ((9494380748601 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((18988761497199 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2677 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2303 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2677 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2303 / 192 : ℚ) : ℝ) ≤ ((9494380748601 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2677 : ((10088619 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2677 / 64 : ℚ) : ℝ) ∧
    logKernel ((2677 / 64 : ℚ) : ℝ) ≤ ((630539 / 4503599627370496 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2677
  constructor
  · exact (show ((10088619 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((18988761497199 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2677 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((9494380748601 / 9223372036854775808 : ℚ) : ℝ) ≤ ((630539 / 4503599627370496 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2678 : ((9347184018569 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((1339 / 32 : ℚ) : ℝ) ∧
    heightZ ((1339 / 32 : ℚ) : ℝ) ≤ ((18694368037141 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((9347184018569 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((1339 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1153 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1339 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1153 / 96 : ℚ) : ℝ) ≤ ((18694368037141 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2678 : ((9778225 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1339 / 32 : ℚ) : ℝ) ∧
    logKernel ((1339 / 32 : ℚ) : ℝ) ≤ ((4889115 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2678
  constructor
  · exact (show ((9778225 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((9347184018569 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1339 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((18694368037141 / 18446744073709551616 : ℚ) : ℝ) ≤ ((4889115 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2679 : ((9202269362315 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2679 / 64 : ℚ) : ℝ) ∧
    heightZ ((2679 / 64 : ℚ) : ℝ) ≤ ((18404538724633 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((9202269362315 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2679 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2309 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2679 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2309 / 192 : ℚ) : ℝ) ≤ ((18404538724633 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2679 : ((9477381 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2679 / 64 : ℚ) : ℝ) ∧
    logKernel ((2679 / 64 : ℚ) : ℝ) ≤ ((4738693 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2679
  constructor
  · exact (show ((9477381 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((9202269362315 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2679 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((18404538724633 / 18446744073709551616 : ℚ) : ℝ) ≤ ((4738693 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2680 : ((18119202799127 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((335 / 8 : ℚ) : ℝ) ∧
    heightZ ((335 / 8 : ℚ) : ℝ) ≤ ((9059601399565 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((18119202799127 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((335 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-289 / 24 : ℚ) : ℝ) ∧
      Real.exp (-((335 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-289 / 24 : ℚ) : ℝ) ≤ ((9059601399565 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2680 : ((17941 / 140737488355328 : ℚ) : ℝ) ≤ logKernel ((335 / 8 : ℚ) : ℝ) ∧
    logKernel ((335 / 8 : ℚ) : ℝ) ≤ ((9185797 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2680
  constructor
  · exact (show ((17941 / 140737488355328 : ℚ) : ℝ) ≤ zKernel ((18119202799127 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((335 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((9059601399565 / 9223372036854775808 : ℚ) : ℝ) ≤ ((9185797 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2681 : ((17838290597119 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2681 / 64 : ℚ) : ℝ) ∧
    heightZ ((2681 / 64 : ℚ) : ℝ) ≤ ((8919145298561 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((17838290597119 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2681 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2315 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2681 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2315 / 192 : ℚ) : ℝ) ≤ ((8919145298561 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2681 : ((8903175 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2681 / 64 : ℚ) : ℝ) ∧
    logKernel ((2681 / 64 : ℚ) : ℝ) ≤ ((2225795 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2681
  constructor
  · exact (show ((8903175 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((17838290597119 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2681 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((8919145298561 / 9223372036854775808 : ℚ) : ℝ) ≤ ((2225795 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2682 : ((8780866767565 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((1341 / 32 : ℚ) : ℝ) ∧
    heightZ ((1341 / 32 : ℚ) : ℝ) ≤ ((17561733535133 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((8780866767565 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((1341 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1159 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1341 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1159 / 96 : ℚ) : ℝ) ≤ ((17561733535133 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2682 : ((8629253 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1341 / 32 : ℚ) : ℝ) ∧
    logKernel ((1341 / 32 : ℚ) : ℝ) ≤ ((4314629 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2682
  constructor
  · exact (show ((8629253 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((8780866767565 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1341 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((17561733535133 / 18446744073709551616 : ℚ) : ℝ) ≤ ((4314629 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2683 : ((8644732046487 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2683 / 64 : ℚ) : ℝ) ∧
    heightZ ((2683 / 64 : ℚ) : ℝ) ≤ ((17289464092977 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((8644732046487 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2683 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2321 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2683 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2321 / 192 : ℚ) : ℝ) ≤ ((17289464092977 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2683 : ((8363759 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2683 / 64 : ℚ) : ℝ) ∧
    logKernel ((2683 / 64 : ℚ) : ℝ) ≤ ((2090941 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2683
  constructor
  · exact (show ((8363759 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((8644732046487 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2683 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((17289464092977 / 18446744073709551616 : ℚ) : ℝ) ≤ ((2090941 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2684 : ((8510707898633 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((671 / 16 : ℚ) : ℝ) ∧
    heightZ ((671 / 16 : ℚ) : ℝ) ≤ ((17021415797269 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((8510707898633 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((671 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-581 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((671 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-581 / 48 : ℚ) : ℝ) ≤ ((17021415797269 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2684 : ((8106433 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((671 / 16 : ℚ) : ℝ) ∧
    logKernel ((671 / 16 : ℚ) : ℝ) ≤ ((4053219 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2684
  constructor
  · exact (show ((8106433 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((8510707898633 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((671 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((17021415797269 / 18446744073709551616 : ℚ) : ℝ) ≤ ((4053219 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2685 : ((4189380801299 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((2685 / 64 : ℚ) : ℝ) ∧
    heightZ ((2685 / 64 : ℚ) : ℝ) ≤ ((16757523205199 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((4189380801299 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((2685 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2327 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2685 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2327 / 192 : ℚ) : ℝ) ≤ ((16757523205199 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2685 : ((61383 / 562949953421312 : ℚ) : ℝ) ≤ logKernel ((2685 / 64 : ℚ) : ℝ) ∧
    logKernel ((2685 / 64 : ℚ) : ℝ) ≤ ((7857029 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2685
  constructor
  · exact (show ((61383 / 562949953421312 : ℚ) : ℝ) ≤ zKernel ((4189380801299 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2685 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((16757523205199 / 18446744073709551616 : ℚ) : ℝ) ≤ ((7857029 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2686 : ((16497721888551 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1343 / 32 : ℚ) : ℝ) ∧
    heightZ ((1343 / 32 : ℚ) : ℝ) ≤ ((8248860944277 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((16497721888551 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1343 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1165 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1343 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1165 / 96 : ℚ) : ℝ) ≤ ((8248860944277 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2686 : ((7615289 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1343 / 32 : ℚ) : ℝ) ∧
    logKernel ((1343 / 32 : ℚ) : ℝ) ≤ ((3807647 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2686
  constructor
  · exact (show ((7615289 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((16497721888551 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1343 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((8248860944277 / 9223372036854775808 : ℚ) : ℝ) ≤ ((3807647 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2687 : ((253780444031 / 288230376151711744 : ℚ) : ℝ) ≤ heightZ ((2687 / 64 : ℚ) : ℝ) ∧
    heightZ ((2687 / 64 : ℚ) : ℝ) ≤ ((16241948417987 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((253780444031 / 288230376151711744 : ℚ) : ℝ) ≤ Real.exp (-((2687 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2333 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2687 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2333 / 192 : ℚ) : ℝ) ≤ ((16241948417987 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2687 : ((7380991 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2687 / 64 : ℚ) : ℝ) ∧
    logKernel ((2687 / 64 : ℚ) : ℝ) ≤ ((1845249 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2687
  constructor
  · exact (show ((7380991 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((253780444031 / 288230376151711744 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2687 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((16241948417987 / 18446744073709551616 : ℚ) : ℝ) ≤ ((1845249 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2688 : ((15990140347531 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((42 / 1 : ℚ) : ℝ) ∧
    heightZ ((42 / 1 : ℚ) : ℝ) ≤ ((7995070173767 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((15990140347531 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((42 / 1 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-73 / 6 : ℚ) : ℝ) ∧
      Real.exp (-((42 / 1 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-73 / 6 : ℚ) : ℝ) ≤ ((7995070173767 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2688 : ((3576951 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((42 / 1 : ℚ) : ℝ) ∧
    logKernel ((42 / 1 : ℚ) : ℝ) ≤ ((7153907 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2688
  constructor
  · exact (show ((3576951 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((15990140347531 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((42 / 1 : ℚ) : ℝ)) hh).trans
      (show zKernel ((7995070173767 / 9223372036854775808 : ℚ) : ℝ) ≤ ((7153907 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2689 : ((15742236199361 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2689 / 64 : ℚ) : ℝ) ∧
    heightZ ((2689 / 64 : ℚ) : ℝ) ≤ ((3935559049841 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((15742236199361 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2689 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2339 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2689 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2339 / 192 : ℚ) : ℝ) ≤ ((3935559049841 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2689 : ((6933799 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2689 / 64 : ℚ) : ℝ) ∧
    logKernel ((2689 / 64 : ℚ) : ℝ) ≤ ((1733451 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2689
  constructor
  · exact (show ((6933799 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((15742236199361 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2689 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((3935559049841 / 4611686018427387904 : ℚ) : ℝ) ≤ ((1733451 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2690 : ((242158991387 / 288230376151711744 : ℚ) : ℝ) ≤ heightZ ((1345 / 32 : ℚ) : ℝ) ∧
    heightZ ((1345 / 32 : ℚ) : ℝ) ≤ ((15498175448771 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((242158991387 / 288230376151711744 : ℚ) : ℝ) ≤ Real.exp (-((1345 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1171 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1345 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1171 / 96 : ℚ) : ℝ) ≤ ((15498175448771 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2690 : ((6720469 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1345 / 32 : ℚ) : ℝ) ∧
    logKernel ((1345 / 32 : ℚ) : ℝ) ≤ ((3360237 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2690
  constructor
  · exact (show ((6720469 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((242158991387 / 288230376151711744 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1345 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((15498175448771 / 18446744073709551616 : ℚ) : ℝ) ≤ ((3360237 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2691 : ((15257898509397 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2691 / 64 : ℚ) : ℝ) ∧
    heightZ ((2691 / 64 : ℚ) : ℝ) ≤ ((1907237313675 / 2305843009213693952 : ℚ) : ℝ) := by
  have h : ((15257898509397 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2691 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2345 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2691 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2345 / 192 : ℚ) : ℝ) ≤ ((1907237313675 / 2305843009213693952 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2691 : ((6513701 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2691 / 64 : ℚ) : ℝ) ∧
    logKernel ((2691 / 64 : ℚ) : ℝ) ≤ ((3256853 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2691
  constructor
  · exact (show ((6513701 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((15257898509397 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2691 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1907237313675 / 2305843009213693952 : ℚ) : ℝ) ≤ ((3256853 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2692 : ((3755336679673 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((673 / 16 : ℚ) : ℝ) ∧
    heightZ ((673 / 16 : ℚ) : ℝ) ≤ ((15021346718695 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((3755336679673 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((673 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-587 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((673 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-587 / 48 : ℚ) : ℝ) ≤ ((15021346718695 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2692 : ((394581 / 4503599627370496 : ℚ) : ℝ) ≤ logKernel ((673 / 16 : ℚ) : ℝ) ∧
    logKernel ((673 / 16 : ℚ) : ℝ) ≤ ((6313301 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2692
  constructor
  · exact (show ((394581 / 4503599627370496 : ℚ) : ℝ) ≤ zKernel ((3755336679673 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((673 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((15021346718695 / 18446744073709551616 : ℚ) : ℝ) ≤ ((6313301 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2693 : ((14788462323575 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2693 / 64 : ℚ) : ℝ) ∧
    heightZ ((2693 / 64 : ℚ) : ℝ) ≤ ((7394231161789 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((14788462323575 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2693 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2351 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2693 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2351 / 192 : ℚ) : ℝ) ≤ ((7394231161789 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2693 : ((382441 / 4503599627370496 : ℚ) : ℝ) ≤ logKernel ((2693 / 64 : ℚ) : ℝ) ∧
    logKernel ((2693 / 64 : ℚ) : ℝ) ≤ ((6119061 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2693
  constructor
  · exact (show ((382441 / 4503599627370496 : ℚ) : ℝ) ≤ zKernel ((14788462323575 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2693 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((7394231161789 / 9223372036854775808 : ℚ) : ℝ) ≤ ((6119061 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2694 : ((3639797116587 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((1347 / 32 : ℚ) : ℝ) ∧
    heightZ ((1347 / 32 : ℚ) : ℝ) ≤ ((14559188466351 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((3639797116587 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((1347 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1177 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1347 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1177 / 96 : ℚ) : ℝ) ≤ ((14559188466351 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2694 : ((741349 / 9007199254740992 : ℚ) : ℝ) ≤ logKernel ((1347 / 32 : ℚ) : ℝ) ∧
    logKernel ((1347 / 32 : ℚ) : ℝ) ≤ ((5930797 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2694
  constructor
  · exact (show ((741349 / 9007199254740992 : ℚ) : ℝ) ≤ zKernel ((3639797116587 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1347 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((14559188466351 / 18446744073709551616 : ℚ) : ℝ) ≤ ((5930797 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2695 : ((7166734585405 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2695 / 64 : ℚ) : ℝ) ∧
    heightZ ((2695 / 64 : ℚ) : ℝ) ≤ ((14333469170813 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((7166734585405 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2695 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2357 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2695 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2357 / 192 : ℚ) : ℝ) ≤ ((14333469170813 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2695 : ((5748321 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2695 / 64 : ℚ) : ℝ) ∧
    logKernel ((2695 / 64 : ℚ) : ℝ) ≤ ((2874163 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2695
  constructor
  · exact (show ((5748321 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((7166734585405 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2695 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((14333469170813 / 18446744073709551616 : ℚ) : ℝ) ≤ ((2874163 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2696 : ((14111249328589 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((337 / 8 : ℚ) : ℝ) ∧
    heightZ ((337 / 8 : ℚ) : ℝ) ≤ ((881953083037 / 1152921504606846976 : ℚ) : ℝ) := by
  have h : ((14111249328589 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((337 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-295 / 24 : ℚ) : ℝ) ∧
      Real.exp (-((337 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-295 / 24 : ℚ) : ℝ) ≤ ((881953083037 / 1152921504606846976 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2696 : ((696433 / 9007199254740992 : ℚ) : ℝ) ≤ logKernel ((337 / 8 : ℚ) : ℝ) ∧
    logKernel ((337 / 8 : ℚ) : ℝ) ≤ ((5571469 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2696
  constructor
  · exact (show ((696433 / 9007199254740992 : ℚ) : ℝ) ≤ zKernel ((14111249328589 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((337 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((881953083037 / 1152921504606846976 : ℚ) : ℝ) ≤ ((5571469 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2697 : ((13892474685691 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2697 / 64 : ℚ) : ℝ) ∧
    heightZ ((2697 / 64 : ℚ) : ℝ) ≤ ((6946237342847 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((13892474685691 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2697 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2363 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2697 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2363 / 192 : ℚ) : ℝ) ≤ ((6946237342847 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2697 : ((337503 / 4503599627370496 : ℚ) : ℝ) ≤ logKernel ((2697 / 64 : ℚ) : ℝ) ∧
    logKernel ((2697 / 64 : ℚ) : ℝ) ≤ ((5400053 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2697
  constructor
  · exact (show ((337503 / 4503599627370496 : ℚ) : ℝ) ≤ zKernel ((13892474685691 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2697 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((6946237342847 / 9223372036854775808 : ℚ) : ℝ) ≤ ((5400053 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2698 : ((13677091829251 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1349 / 32 : ℚ) : ℝ) ∧
    heightZ ((1349 / 32 : ℚ) : ℝ) ≤ ((6838545914627 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((13677091829251 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1349 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1183 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1349 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1183 / 96 : ℚ) : ℝ) ≤ ((6838545914627 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2698 : ((2616953 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((1349 / 32 : ℚ) : ℝ) ∧
    logKernel ((1349 / 32 : ℚ) : ℝ) ≤ ((5233911 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2698
  constructor
  · exact (show ((2616953 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((13677091829251 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1349 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((6838545914627 / 9223372036854775808 : ℚ) : ℝ) ≤ ((5233911 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2699 : ((13465048174493 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2699 / 64 : ℚ) : ℝ) ∧
    heightZ ((2699 / 64 : ℚ) : ℝ) ≤ ((420782755453 / 576460752303423488 : ℚ) : ℝ) := by
  have h : ((13465048174493 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2699 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2369 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2699 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2369 / 192 : ℚ) : ℝ) ≤ ((420782755453 / 576460752303423488 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2699 : ((5072875 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2699 / 64 : ℚ) : ℝ) ∧
    logKernel ((2699 / 64 : ℚ) : ℝ) ≤ ((317055 / 4503599627370496 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2699
  constructor
  · exact (show ((5072875 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((13465048174493 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2699 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((420782755453 / 576460752303423488 : ℚ) : ℝ) ≤ ((317055 / 4503599627370496 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2700 : ((6628145975947 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((675 / 16 : ℚ) : ℝ) ∧
    heightZ ((675 / 16 : ℚ) : ℝ) ≤ ((13256291951897 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((6628145975947 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((675 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-593 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((675 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-593 / 48 : ℚ) : ℝ) ≤ ((13256291951897 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2700 : ((4916799 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((675 / 16 : ℚ) : ℝ) ∧
    logKernel ((675 / 16 : ℚ) : ℝ) ≤ ((1229201 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2700
  constructor
  · exact (show ((4916799 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((6628145975947 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((675 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((13256291951897 / 18446744073709551616 : ℚ) : ℝ) ≤ ((1229201 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2701 : ((13050772194543 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2701 / 64 : ℚ) : ℝ) ∧
    heightZ ((2701 / 64 : ℚ) : ℝ) ≤ ((6525386097273 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((13050772194543 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2701 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2375 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2701 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2375 / 192 : ℚ) : ℝ) ≤ ((6525386097273 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2701 : ((4765525 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2701 / 64 : ℚ) : ℝ) ∧
    logKernel ((2701 / 64 : ℚ) : ℝ) ≤ ((2382765 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2701
  constructor
  · exact (show ((4765525 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((13050772194543 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2701 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((6525386097273 / 9223372036854775808 : ℚ) : ℝ) ≤ ((2382765 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2702 : ((12848438725697 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1351 / 32 : ℚ) : ℝ) ∧
    heightZ ((1351 / 32 : ℚ) : ℝ) ≤ ((3212109681425 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((12848438725697 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1351 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1189 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1351 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1189 / 96 : ℚ) : ℝ) ≤ ((3212109681425 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2702 : ((4618905 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1351 / 32 : ℚ) : ℝ) ∧
    logKernel ((1351 / 32 : ℚ) : ℝ) ≤ ((2309455 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2702
  constructor
  · exact (show ((4618905 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((12848438725697 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1351 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((3212109681425 / 4611686018427387904 : ℚ) : ℝ) ≤ ((2309455 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2703 : ((12649242146531 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2703 / 64 : ℚ) : ℝ) ∧
    heightZ ((2703 / 64 : ℚ) : ℝ) ≤ ((6324621073267 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((12649242146531 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2703 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2381 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2703 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2381 / 192 : ℚ) : ℝ) ≤ ((6324621073267 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2703 : ((1119199 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((2703 / 64 : ℚ) : ℝ) ∧
    logKernel ((2703 / 64 : ℚ) : ℝ) ≤ ((4476801 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2703
  constructor
  · exact (show ((1119199 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((12649242146531 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2703 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((6324621073267 / 9223372036854775808 : ℚ) : ℝ) ≤ ((4476801 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2704 : ((12453133824079 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((169 / 4 : ℚ) : ℝ) ∧
    heightZ ((169 / 4 : ℚ) : ℝ) ≤ ((6226566912041 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((12453133824079 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((169 / 4 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-149 / 12 : ℚ) : ℝ) ∧
      Real.exp (-((169 / 4 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-149 / 12 : ℚ) : ℝ) ≤ ((6226566912041 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2704 : ((1084765 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((169 / 4 : ℚ) : ℝ) ∧
    logKernel ((169 / 4 : ℚ) : ℝ) ≤ ((4339065 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2704
  constructor
  · exact (show ((1084765 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((12453133824079 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((169 / 4 : ℚ) : ℝ)) hh).trans
      (show zKernel ((6226566912041 / 9223372036854775808 : ℚ) : ℝ) ≤ ((4339065 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

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

theorem log_height_bounds_832 : ((134475599641338697 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((1337 / 32 : ℚ) : ℝ) ∧
    Real.log ((1337 / 32 : ℚ) : ℝ) ≤ ((268951199282677397 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((134475599641338697 / 36028797018963968 : ℚ) : ℝ) ≤ ((1337 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1337 / 32 : ℚ) : ℝ) ≤ Real.exp ((268951199282677397 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_832 : heightPower (832 : Fin 988) ≤ ((470523164943641 / 35184372088832 : ℚ) : ℝ) := by
  have hh := log_height_bounds_832
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_832 : heightFactor (832 : Fin 988) ≤ ((103493413 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_832
  obtain ⟨hpl, hph⟩ := kernel_bounds_2673
  obtain ⟨hcl, hch⟩ := kernel_bounds_2674
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2674
  have h : (((1787569 / 512 : ℚ) : ℝ) * (logKernel ((2673 / 64 : ℚ) : ℝ) - logKernel ((1337 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1337 / 32 : ℚ) : ℝ) + Real.log ((1337 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((103493413 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_833 : ((134489070868647991 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2675 / 64 : ℚ) : ℝ) ∧
    Real.log ((2675 / 64 : ℚ) : ℝ) ≤ ((268978141737295985 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((134489070868647991 / 36028797018963968 : ℚ) : ℝ) ≤ ((2675 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2675 / 64 : ℚ) : ℝ) ≤ Real.exp ((268978141737295985 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_833 : heightPower (833 : Fin 988) ≤ ((1884344305011793 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_833
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_833 : heightFactor (833 : Fin 988) ≤ ((201842957 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_833
  obtain ⟨hpl, hph⟩ := kernel_bounds_2674
  obtain ⟨hcl, hch⟩ := kernel_bounds_2675
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2675
  have h : (((7155625 / 2048 : ℚ) : ℝ) * (logKernel ((1337 / 32 : ℚ) : ℝ) - logKernel ((2675 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2675 / 64 : ℚ) : ℝ) + Real.log ((2675 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((201842957 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_834 : ((269005074121850939 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((669 / 16 : ℚ) : ℝ) ∧
    Real.log ((669 / 16 : ℚ) : ℝ) ≤ ((134502537060925471 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((269005074121850939 / 72057594037927936 : ℚ) : ℝ) ≤ ((669 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((669 / 16 : ℚ) : ℝ) ≤ Real.exp ((134502537060925471 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_834 : heightPower (834 : Fin 988) ≤ ((1886595930580929 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_834
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_834 : heightFactor (834 : Fin 988) ≤ ((393653751 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_834
  obtain ⟨hpl, hph⟩ := kernel_bounds_2675
  obtain ⟨hcl, hch⟩ := kernel_bounds_2676
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2676
  have h : (((447561 / 128 : ℚ) : ℝ) * (logKernel ((2675 / 64 : ℚ) : ℝ) - logKernel ((669 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((669 / 16 : ℚ) : ℝ) + Real.log ((669 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((393653751 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_835 : ((33628999555483383 / 9007199254740992 : ℚ) : ℝ) ≤ Real.log ((2677 / 64 : ℚ) : ℝ) ∧
    Real.log ((2677 / 64 : ℚ) : ℝ) ≤ ((269031996443867067 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((33628999555483383 / 9007199254740992 : ℚ) : ℝ) ≤ ((2677 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2677 / 64 : ℚ) : ℝ) ≤ Real.exp ((269031996443867067 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_835 : heightPower (835 : Fin 988) ≤ ((3777695072993337 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_835
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_835 : heightFactor (835 : Fin 988) ≤ ((11995963 / 8796093022208 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_835
  obtain ⟨hpl, hph⟩ := kernel_bounds_2676
  obtain ⟨hcl, hch⟩ := kernel_bounds_2677
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2677
  have h : (((7166329 / 2048 : ℚ) : ℝ) * (logKernel ((669 / 16 : ℚ) : ℝ) - logKernel ((2677 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2677 / 64 : ℚ) : ℝ) + Real.log ((2677 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((11995963 / 8796093022208 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_836 : ((33632363588857591 / 9007199254740992 : ℚ) : ℝ) ≤ Real.log ((1339 / 32 : ℚ) : ℝ) ∧
    Real.log ((1339 / 32 : ℚ) : ℝ) ≤ ((269058908710860731 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((33632363588857591 / 9007199254740992 : ℚ) : ℝ) ≤ ((1339 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1339 / 32 : ℚ) : ℝ) ≤ Real.exp ((269058908710860731 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_836 : heightPower (836 : Fin 988) ≤ ((3782198245547385 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_836
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_836 : heightFactor (836 : Fin 988) ≤ ((187165461 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_836
  obtain ⟨hpl, hph⟩ := kernel_bounds_2677
  obtain ⟨hcl, hch⟩ := kernel_bounds_2678
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2678
  have h : (((1792921 / 512 : ℚ) : ℝ) * (logKernel ((2677 / 64 : ℚ) : ℝ) - logKernel ((1339 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1339 / 32 : ℚ) : ℝ) + Real.log ((1339 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((187165461 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_837 : ((269085810930339879 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2679 / 64 : ℚ) : ℝ) ∧
    Real.log ((2679 / 64 : ℚ) : ℝ) ≤ ((134542905465169941 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((269085810930339879 / 72057594037927936 : ℚ) : ℝ) ≤ ((2679 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2679 / 64 : ℚ) : ℝ) ≤ Real.exp ((134542905465169941 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_837 : heightPower (837 : Fin 988) ≤ ((1893350689426665 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_837
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_837 : heightFactor (837 : Fin 988) ≤ ((182514017 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_837
  obtain ⟨hpl, hph⟩ := kernel_bounds_2678
  obtain ⟨hcl, hch⟩ := kernel_bounds_2679
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2679
  have h : (((7177041 / 2048 : ℚ) : ℝ) * (logKernel ((1339 / 32 : ℚ) : ℝ) - logKernel ((2679 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2679 / 64 : ℚ) : ℝ) + Real.log ((2679 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((182514017 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_838 : ((8409771972181377 / 2251799813685248 : ℚ) : ℝ) ≤ Real.log ((335 / 8 : ℚ) : ℝ) ∧
    Real.log ((335 / 8 : ℚ) : ℝ) ≤ ((269112703109804067 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((8409771972181377 / 2251799813685248 : ℚ) : ℝ) ≤ ((335 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((335 / 8 : ℚ) : ℝ) ≤ Real.exp ((269112703109804067 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_838 : heightPower (838 : Fin 988) ≤ ((1895602236470233 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_838
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_838 : heightFactor (838 : Fin 988) ≤ ((177978133 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_838
  obtain ⟨hpl, hph⟩ := kernel_bounds_2679
  obtain ⟨hcl, hch⟩ := kernel_bounds_2680
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2680
  have h : (((112225 / 32 : ℚ) : ℝ) * (logKernel ((2679 / 64 : ℚ) : ℝ) - logKernel ((335 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((335 / 8 : ℚ) : ℝ) + Real.log ((335 / 8 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((177978133 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_839 : ((134569792628372217 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2681 / 64 : ℚ) : ℝ) ∧
    Real.log ((2681 / 64 : ℚ) : ℝ) ≤ ((269139585256744437 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((134569792628372217 / 36028797018963968 : ℚ) : ℝ) ≤ ((2681 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2681 / 64 : ℚ) : ℝ) ≤ Real.exp ((269139585256744437 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_839 : heightPower (839 : Fin 988) ≤ ((3795707527838055 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_839
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_839 : heightFactor (839 : Fin 988) ≤ ((43388735 / 35184372088832 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_839
  obtain ⟨hpl, hph⟩ := kernel_bounds_2680
  obtain ⟨hcl, hch⟩ := kernel_bounds_2681
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2681
  have h : (((7187761 / 2048 : ℚ) : ℝ) * (logKernel ((335 / 8 : ℚ) : ℝ) - logKernel ((2681 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2681 / 64 : ℚ) : ℝ) + Real.log ((2681 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((43388735 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_840 : ((269166457378643757 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1341 / 32 : ℚ) : ℝ) ∧
    Real.log ((1341 / 32 : ℚ) : ℝ) ≤ ((16822903586165235 / 4503599627370496 : ℚ) : ℝ) := by
  have hl : Real.exp ((269166457378643757 / 72057594037927936 : ℚ) : ℝ) ≤ ((1341 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1341 / 32 : ℚ) : ℝ) ≤ Real.exp ((16822903586165235 / 4503599627370496 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_840 : heightPower (840 : Fin 988) ≤ ((3800210543575329 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_840
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_840 : heightFactor (840 : Fin 988) ≤ ((169241639 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_840
  obtain ⟨hpl, hph⟩ := kernel_bounds_2681
  obtain ⟨hcl, hch⟩ := kernel_bounds_2682
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2682
  have h : (((1798281 / 512 : ℚ) : ℝ) * (logKernel ((2681 / 64 : ℚ) : ℝ) - logKernel ((1341 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1341 / 32 : ℚ) : ℝ) + Real.log ((1341 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((169241639 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_841 : ((269193319482976437 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2683 / 64 : ℚ) : ℝ) ∧
    Real.log ((2683 / 64 : ℚ) : ℝ) ≤ ((33649164935372055 / 9007199254740992 : ℚ) : ℝ) := by
  have hl : Real.exp ((269193319482976437 / 72057594037927936 : ℚ) : ℝ) ≤ ((2683 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2683 / 64 : ℚ) : ℝ) ≤ Real.exp ((33649164935372055 / 9007199254740992 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_841 : heightPower (841 : Fin 988) ≤ ((1902356760090741 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_841
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_841 : heightFactor (841 : Fin 988) ≤ ((82517751 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_841
  obtain ⟨hpl, hph⟩ := kernel_bounds_2682
  obtain ⟨hcl, hch⟩ := kernel_bounds_2683
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2683
  have h : (((7198489 / 2048 : ℚ) : ℝ) * (logKernel ((1341 / 32 : ℚ) : ℝ) - logKernel ((2683 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2683 / 64 : ℚ) : ℝ) + Real.log ((2683 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((82517751 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_842 : ((269220171577208519 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((671 / 16 : ℚ) : ℝ) ∧
    Real.log ((671 / 16 : ℚ) : ℝ) ≤ ((134610085788604261 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((269220171577208519 / 72057594037927936 : ℚ) : ℝ) ≤ ((671 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((671 / 16 : ℚ) : ℝ) ≤ Real.exp ((134610085788604261 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_842 : heightPower (842 : Fin 988) ≤ ((238076028605355 / 17592186044416 : ℚ) : ℝ) := by
  have hh := log_height_bounds_842
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_842 : heightFactor (842 : Fin 988) ≤ ((321867735 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_842
  obtain ⟨hpl, hph⟩ := kernel_bounds_2683
  obtain ⟨hcl, hch⟩ := kernel_bounds_2684
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2684
  have h : (((450241 / 128 : ℚ) : ℝ) * (logKernel ((2683 / 64 : ℚ) : ℝ) - logKernel ((671 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((671 / 16 : ℚ) : ℝ) + Real.log ((671 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((321867735 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_843 : ((134623506834398853 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2685 / 64 : ℚ) : ℝ) ∧
    Real.log ((2685 / 64 : ℚ) : ℝ) ≤ ((269247013668797709 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((134623506834398853 / 36028797018963968 : ℚ) : ℝ) ≤ ((2685 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2685 / 64 : ℚ) : ℝ) ≤ Real.exp ((269247013668797709 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_843 : heightPower (843 : Fin 988) ≤ ((3813719356117055 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_843
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_843 : heightFactor (843 : Fin 988) ≤ ((156934141 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_843
  obtain ⟨hpl, hph⟩ := kernel_bounds_2684
  obtain ⟨hcl, hch⟩ := kernel_bounds_2685
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2685
  have h : (((7209225 / 2048 : ℚ) : ℝ) * (logKernel ((671 / 16 : ℚ) : ℝ) - logKernel ((2685 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2685 / 64 : ℚ) : ℝ) + Real.log ((2685 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((156934141 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_844 : ((33659230720649171 / 9007199254740992 : ℚ) : ℝ) ≤ Real.log ((1343 / 32 : ℚ) : ℝ) ∧
    Real.log ((1343 / 32 : ℚ) : ℝ) ≤ ((269273845765193371 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((33659230720649171 / 9007199254740992 : ℚ) : ℝ) ≤ ((1343 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1343 / 32 : ℚ) : ℝ) ≤ Real.exp ((269273845765193371 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_844 : heightPower (844 : Fin 988) ≤ ((59659722117261 / 4398046511104 : ℚ) : ℝ) := by
  have hh := log_height_bounds_844
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_844 : heightFactor (844 : Fin 988) ≤ ((153033791 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_844
  obtain ⟨hpl, hph⟩ := kernel_bounds_2685
  obtain ⟨hcl, hch⟩ := kernel_bounds_2686
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2686
  have h : (((1803649 / 512 : ℚ) : ℝ) * (logKernel ((2685 / 64 : ℚ) : ℝ) - logKernel ((1343 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1343 / 32 : ℚ) : ℝ) + Real.log ((1343 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((153033791 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_845 : ((134650333936918279 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2687 / 64 : ℚ) : ℝ) ∧
    Real.log ((2687 / 64 : ℚ) : ℝ) ≤ ((269300667873836561 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((134650333936918279 / 36028797018963968 : ℚ) : ℝ) ≤ ((2687 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2687 / 64 : ℚ) : ℝ) ≤ Real.exp ((269300667873836561 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_845 : heightPower (845 : Fin 988) ≤ ((59730078685589 / 4398046511104 : ℚ) : ℝ) := by
  have hh := log_height_bounds_845
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_845 : heightFactor (845 : Fin 988) ≤ ((74615175 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_845
  obtain ⟨hpl, hph⟩ := kernel_bounds_2686
  obtain ⟨hcl, hch⟩ := kernel_bounds_2687
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2687
  have h : (((7219969 / 2048 : ℚ) : ℝ) * (logKernel ((1343 / 32 : ℚ) : ℝ) - logKernel ((2687 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2687 / 64 : ℚ) : ℝ) + Real.log ((2687 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((74615175 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_846 : ((269327480002160023 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((42 / 1 : ℚ) : ℝ) ∧
    Real.log ((42 / 1 : ℚ) : ℝ) ≤ ((134663740001080013 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((269327480002160023 / 72057594037927936 : ℚ) : ℝ) ≤ ((42 / 1 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((42 / 1 : ℚ) : ℝ) ≤ Real.exp ((134663740001080013 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_846 : heightPower (846 : Fin 988) ≤ ((3827227817265063 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_846
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_846 : heightFactor (846 : Fin 988) ≤ ((291042823 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_846
  obtain ⟨hpl, hph⟩ := kernel_bounds_2687
  obtain ⟨hcl, hch⟩ := kernel_bounds_2688
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2688
  have h : (((3528 / 1 : ℚ) : ℝ) * (logKernel ((2687 / 64 : ℚ) : ℝ) - logKernel ((42 / 1 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((42 / 1 : ℚ) : ℝ) + Real.log ((42 / 1 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((291042823 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_847 : ((269354282157588215 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2689 / 64 : ℚ) : ℝ) ∧
    Real.log ((2689 / 64 : ℚ) : ℝ) ≤ ((134677141078794109 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((269354282157588215 / 72057594037927936 : ℚ) : ℝ) ≤ ((2689 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2689 / 64 : ℚ) : ℝ) ≤ Real.exp ((134677141078794109 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_847 : heightPower (847 : Fin 988) ≤ ((59870789995247 / 4398046511104 : ℚ) : ℝ) := by
  have hh := log_height_bounds_847
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_847 : heightFactor (847 : Fin 988) ≤ ((283809257 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_847
  obtain ⟨hpl, hph⟩ := kernel_bounds_2688
  obtain ⟨hcl, hch⟩ := kernel_bounds_2689
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2689
  have h : (((7230721 / 2048 : ℚ) : ℝ) * (logKernel ((42 / 1 : ℚ) : ℝ) - logKernel ((2689 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2689 / 64 : ℚ) : ℝ) + Real.log ((2689 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((283809257 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_848 : ((33672634293442163 / 9007199254740992 : ℚ) : ℝ) ≤ Real.log ((1345 / 32 : ℚ) : ℝ) ∧
    Real.log ((1345 / 32 : ℚ) : ℝ) ≤ ((269381074347537307 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((33672634293442163 / 9007199254740992 : ℚ) : ℝ) ≤ ((1345 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1345 / 32 : ℚ) : ℝ) ≤ Real.exp ((269381074347537307 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_848 : heightPower (848 : Fin 988) ≤ ((3836233263198901 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_848
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_848 : heightFactor (848 : Fin 988) ≤ ((276755425 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_848
  obtain ⟨hpl, hph⟩ := kernel_bounds_2689
  obtain ⟨hcl, hch⟩ := kernel_bounds_2690
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2690
  have h : (((1809025 / 512 : ℚ) : ℝ) * (logKernel ((2689 / 64 : ℚ) : ℝ) - logKernel ((1345 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1345 / 32 : ℚ) : ℝ) + Real.log ((1345 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((276755425 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_849 : ((33675982072426899 / 9007199254740992 : ℚ) : ℝ) ≤ Real.log ((2691 / 64 : ℚ) : ℝ) ∧
    Real.log ((2691 / 64 : ℚ) : ℝ) ≤ ((269407856579415195 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((33675982072426899 / 9007199254740992 : ℚ) : ℝ) ≤ ((2691 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2691 / 64 : ℚ) : ℝ) ≤ Real.exp ((269407856579415195 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_849 : heightPower (849 : Fin 988) ≤ ((1920367963901639 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_849
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_849 : heightFactor (849 : Fin 988) ≤ ((269876863 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_849
  obtain ⟨hpl, hph⟩ := kernel_bounds_2690
  obtain ⟨hcl, hch⟩ := kernel_bounds_2691
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2691
  have h : (((7241481 / 2048 : ℚ) : ℝ) * (logKernel ((1345 / 32 : ℚ) : ℝ) - logKernel ((2691 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2691 / 64 : ℚ) : ℝ) + Real.log ((2691 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((269876863 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_850 : ((67358657215155381 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((673 / 16 : ℚ) : ℝ) ∧
    Real.log ((673 / 16 : ℚ) : ℝ) ≤ ((269434628860621527 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((67358657215155381 / 18014398509481984 : ℚ) : ℝ) ≤ ((673 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((673 / 16 : ℚ) : ℝ) ≤ Real.exp ((269434628860621527 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_850 : heightPower (850 : Fin 988) ≤ ((961309638384461 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_850
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_850 : heightFactor (850 : Fin 988) ≤ ((263169219 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_850
  obtain ⟨hpl, hph⟩ := kernel_bounds_2691
  obtain ⟨hcl, hch⟩ := kernel_bounds_2692
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2692
  have h : (((452929 / 128 : ℚ) : ℝ) * (logKernel ((2691 / 64 : ℚ) : ℝ) - logKernel ((673 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((673 / 16 : ℚ) : ℝ) + Real.log ((673 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((263169219 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_851 : ((67365347799636925 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((2693 / 64 : ℚ) : ℝ) ∧
    Real.log ((2693 / 64 : ℚ) : ℝ) ≤ ((269461391198547703 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((67365347799636925 / 18014398509481984 : ℚ) : ℝ) ≤ ((2693 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2693 / 64 : ℚ) : ℝ) ≤ Real.exp ((269461391198547703 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_851 : heightPower (851 : Fin 988) ≤ ((240608821276967 / 17592186044416 : ℚ) : ℝ) := by
  have hh := log_height_bounds_851
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_851 : heightFactor (851 : Fin 988) ≤ ((32078531 / 35184372088832 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_851
  obtain ⟨hpl, hph⟩ := kernel_bounds_2692
  obtain ⟨hcl, hch⟩ := kernel_bounds_2693
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2693
  have h : (((7252249 / 2048 : ℚ) : ℝ) * (logKernel ((673 / 16 : ℚ) : ℝ) - logKernel ((2693 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2693 / 64 : ℚ) : ℝ) + Real.log ((2693 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((32078531 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_852 : ((269488143600576885 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1347 / 32 : ℚ) : ℝ) ∧
    Real.log ((1347 / 32 : ℚ) : ℝ) ≤ ((33686017950072111 / 9007199254740992 : ℚ) : ℝ) := by
  have hl : Real.exp ((269488143600576885 / 72057594037927936 : ℚ) : ℝ) ≤ ((1347 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1347 / 32 : ℚ) : ℝ) ≤ Real.exp ((33686017950072111 / 9007199254740992 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_852 : heightPower (852 : Fin 988) ≤ ((3854243688513003 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_852
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_852 : heightFactor (852 : Fin 988) ≤ ((125124905 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_852
  obtain ⟨hpl, hph⟩ := kernel_bounds_2693
  obtain ⟨hcl, hch⟩ := kernel_bounds_2694
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2694
  have h : (((1814409 / 512 : ℚ) : ℝ) * (logKernel ((2693 / 64 : ℚ) : ℝ) - logKernel ((1347 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1347 / 32 : ℚ) : ℝ) + Real.log ((1347 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((125124905 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_853 : ((269514886074084029 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2695 / 64 : ℚ) : ℝ) ∧
    Real.log ((2695 / 64 : ℚ) : ℝ) ≤ ((4211170094907563 / 1125899906842624 : ℚ) : ℝ) := by
  have hl : Real.exp ((269514886074084029 / 72057594037927936 : ℚ) : ℝ) ≤ ((2695 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2695 / 64 : ℚ) : ℝ) ≤ Real.exp ((4211170094907563 / 1125899906842624 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_853 : heightPower (853 : Fin 988) ≤ ((964686549452811 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_853
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_853 : heightFactor (853 : Fin 988) ≤ ((61007467 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_853
  obtain ⟨hpl, hph⟩ := kernel_bounds_2694
  obtain ⟨hcl, hch⟩ := kernel_bounds_2695
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2695
  have h : (((7263025 / 2048 : ℚ) : ℝ) * (logKernel ((1347 / 32 : ℚ) : ℝ) - logKernel ((2695 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2695 / 64 : ℚ) : ℝ) + Real.log ((2695 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((61007467 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_854 : ((67385404656608967 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((337 / 8 : ℚ) : ℝ) ∧
    Real.log ((337 / 8 : ℚ) : ℝ) ≤ ((269541618626435871 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((67385404656608967 / 18014398509481984 : ℚ) : ℝ) ≤ ((337 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((337 / 8 : ℚ) : ℝ) ≤ Real.exp ((269541618626435871 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_854 : heightPower (854 : Fin 988) ≤ ((3863248668354973 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_854
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_854 : heightFactor (854 : Fin 988) ≤ ((237964487 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_854
  obtain ⟨hpl, hph⟩ := kernel_bounds_2695
  obtain ⟨hcl, hch⟩ := kernel_bounds_2696
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2696
  have h : (((113569 / 32 : ℚ) : ℝ) * (logKernel ((2695 / 64 : ℚ) : ℝ) - logKernel ((337 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((337 / 8 : ℚ) : ℝ) + Real.log ((337 / 8 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((237964487 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_855 : ((67392085316247737 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((2697 / 64 : ℚ) : ℝ) ∧
    Real.log ((2697 / 64 : ℚ) : ℝ) ≤ ((269568341264990951 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((67392085316247737 / 18014398509481984 : ℚ) : ℝ) ≤ ((2697 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2697 / 64 : ℚ) : ℝ) ≤ Real.exp ((269568341264990951 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_855 : heightPower (855 : Fin 988) ≤ ((966937775043233 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_855
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_855 : heightFactor (855 : Fin 988) ≤ ((58012457 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_855
  obtain ⟨hpl, hph⟩ := kernel_bounds_2696
  obtain ⟨hcl, hch⟩ := kernel_bounds_2697
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2697
  have h : (((7273809 / 2048 : ℚ) : ℝ) * (logKernel ((337 / 8 : ℚ) : ℝ) - logKernel ((2697 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2697 / 64 : ℚ) : ℝ) + Real.log ((2697 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((58012457 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_856 : ((134797526998549813 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((1349 / 32 : ℚ) : ℝ) ∧
    Real.log ((1349 / 32 : ℚ) : ℝ) ≤ ((269595053997099629 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((134797526998549813 / 36028797018963968 : ℚ) : ℝ) ≤ ((1349 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1349 / 32 : ℚ) : ℝ) ≤ Real.exp ((269595053997099629 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_856 : heightPower (856 : Fin 988) ≤ ((968063373323459 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_856
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_856 : heightFactor (856 : Fin 988) ≤ ((113141073 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_856
  obtain ⟨hpl, hph⟩ := kernel_bounds_2697
  obtain ⟨hcl, hch⟩ := kernel_bounds_2698
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2698
  have h : (((1819801 / 512 : ℚ) : ℝ) * (logKernel ((2697 / 64 : ℚ) : ℝ) - logKernel ((1349 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1349 / 32 : ℚ) : ℝ) + Real.log ((1349 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((113141073 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_857 : ((134810878415052045 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2699 / 64 : ℚ) : ℝ) ∧
    Real.log ((2699 / 64 : ℚ) : ℝ) ≤ ((269621756830104093 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((134810878415052045 / 36028797018963968 : ℚ) : ℝ) ≤ ((2699 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2699 / 64 : ℚ) : ℝ) ≤ Real.exp ((269621756830104093 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_857 : heightPower (857 : Fin 988) ≤ ((969188961936591 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_857
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_857 : heightFactor (857 : Fin 988) ≤ ((220657793 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_857
  obtain ⟨hpl, hph⟩ := kernel_bounds_2698
  obtain ⟨hcl, hch⟩ := kernel_bounds_2699
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2699
  have h : (((7284601 / 2048 : ℚ) : ℝ) * (logKernel ((1349 / 32 : ℚ) : ℝ) - logKernel ((2699 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2699 / 64 : ℚ) : ℝ) + Real.log ((2699 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((220657793 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_858 : ((134824224885669185 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((675 / 16 : ℚ) : ℝ) ∧
    Real.log ((675 / 16 : ℚ) : ℝ) ≤ ((269648449771338373 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((134824224885669185 / 36028797018963968 : ℚ) : ℝ) ≤ ((675 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((675 / 16 : ℚ) : ℝ) ≤ Real.exp ((269648449771338373 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_858 : heightPower (858 : Fin 988) ≤ ((970314540889791 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_858
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_858 : heightFactor (858 : Fin 988) ≤ ((215173207 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_858
  obtain ⟨hpl, hph⟩ := kernel_bounds_2699
  obtain ⟨hcl, hch⟩ := kernel_bounds_2700
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2700
  have h : (((455625 / 128 : ℚ) : ℝ) * (logKernel ((2699 / 64 : ℚ) : ℝ) - logKernel ((675 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((675 / 16 : ℚ) : ℝ) + Real.log ((675 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((215173207 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_859 : ((33709391603516043 / 9007199254740992 : ℚ) : ℝ) ≤ Real.log ((2701 / 64 : ℚ) : ℝ) ∧
    Real.log ((2701 / 64 : ℚ) : ℝ) ≤ ((269675132828128347 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((33709391603516043 / 9007199254740992 : ℚ) : ℝ) ≤ ((2701 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2701 / 64 : ℚ) : ℝ) ≤ Real.exp ((269675132828128347 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_859 : heightPower (859 : Fin 988) ≤ ((1942880220380427 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_859
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_859 : heightFactor (859 : Fin 988) ≤ ((209824917 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_859
  obtain ⟨hpl, hph⟩ := kernel_bounds_2700
  obtain ⟨hcl, hch⟩ := kernel_bounds_2701
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2701
  have h : (((7295401 / 2048 : ℚ) : ℝ) * (logKernel ((675 / 16 : ℚ) : ℝ) - logKernel ((2701 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2701 / 64 : ℚ) : ℝ) + Real.log ((2701 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((209824917 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_860 : ((16856362875486985 / 4503599627370496 : ℚ) : ℝ) ≤ Real.log ((1351 / 32 : ℚ) : ℝ) ∧
    Real.log ((1351 / 32 : ℚ) : ℝ) ≤ ((269701806007791763 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((16856362875486985 / 4503599627370496 : ℚ) : ℝ) ≤ ((1351 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1351 / 32 : ℚ) : ℝ) ≤ Real.exp ((269701806007791763 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_860 : heightPower (860 : Fin 988) ≤ ((1945131339690009 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_860
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_860 : heightFactor (860 : Fin 988) ≤ ((204609537 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_860
  obtain ⟨hpl, hph⟩ := kernel_bounds_2701
  obtain ⟨hcl, hch⟩ := kernel_bounds_2702
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2702
  have h : (((1825201 / 512 : ℚ) : ℝ) * (logKernel ((2701 / 64 : ℚ) : ℝ) - logKernel ((1351 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1351 / 32 : ℚ) : ℝ) + Real.log ((1351 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((204609537 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_861 : ((134864234658819119 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2703 / 64 : ℚ) : ℝ) ∧
    Real.log ((2703 / 64 : ℚ) : ℝ) ≤ ((269728469317638241 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((134864234658819119 / 36028797018963968 : ℚ) : ℝ) ≤ ((2703 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2703 / 64 : ℚ) : ℝ) ≤ Real.exp ((269728469317638241 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_861 : heightPower (861 : Fin 988) ≤ ((1947382439722605 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_861
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_861 : heightFactor (861 : Fin 988) ≤ ((24940471 / 35184372088832 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_861
  obtain ⟨hpl, hph⟩ := kernel_bounds_2702
  obtain ⟨hcl, hch⟩ := kernel_bounds_2703
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2703
  have h : (((7306209 / 2048 : ℚ) : ℝ) * (logKernel ((1351 / 32 : ℚ) : ℝ) - logKernel ((2703 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2703 / 64 : ℚ) : ℝ) + Real.log ((2703 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((24940471 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_862 : ((269755122764969291 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((169 / 4 : ℚ) : ℝ) ∧
    Real.log ((169 / 4 : ℚ) : ℝ) ≤ ((134877561382484647 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((269755122764969291 / 72057594037927936 : ℚ) : ℝ) ≤ ((169 / 4 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((169 / 4 : ℚ) : ℝ) ≤ Real.exp ((134877561382484647 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_862 : heightPower (862 : Fin 988) ≤ ((3899267040984951 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_862
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_862 : heightFactor (862 : Fin 988) ≤ ((48641097 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_862
  obtain ⟨hpl, hph⟩ := kernel_bounds_2703
  obtain ⟨hcl, hch⟩ := kernel_bounds_2704
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2704
  have h : (((28561 / 8 : ℚ) : ℝ) * (logKernel ((2703 / 64 : ℚ) : ℝ) - logKernel ((169 / 4 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((169 / 4 : ℚ) : ℝ) + Real.log ((169 / 4 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((48641097 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_863 : ((269781766357078329 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2705 / 64 : ℚ) : ℝ) ∧
    Real.log ((2705 / 64 : ℚ) : ℝ) ≤ ((67445441589269583 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((269781766357078329 / 72057594037927936 : ℚ) : ℝ) ≤ ((2705 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2705 / 64 : ℚ) : ℝ) ≤ Real.exp ((67445441589269583 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_863 : heightPower (863 : Fin 988) ≤ ((3903769164027731 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_863
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_863 : heightFactor (863 : Fin 988) ≤ ((189728259 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_863
  obtain ⟨hpl, hph⟩ := kernel_bounds_2704
  obtain ⟨hcl, hch⟩ := kernel_bounds_2705
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2705
  have h : (((7317025 / 2048 : ℚ) : ℝ) * (logKernel ((169 / 4 : ℚ) : ℝ) - logKernel ((2705 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2705 / 64 : ℚ) : ℝ) + Real.log ((2705 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((189728259 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

end LegendreK6.M2Pilot.Enclosures.Height026
