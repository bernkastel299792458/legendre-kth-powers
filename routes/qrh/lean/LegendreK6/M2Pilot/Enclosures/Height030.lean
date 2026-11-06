import LegendreK6.M2PilotDefinitions
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp

/-! Generated proposals: every bound is checked by Lean, not by trusting Arb. -/
namespace LegendreK6.M2Pilot.Enclosures.Height030
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem height_z_bounds_2801 : ((1367795231545 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2801 / 64 : ℚ) : ℝ) ∧
    heightZ ((2801 / 64 : ℚ) : ℝ) ≤ ((2735590463093 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((1367795231545 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2801 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2675 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2801 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2675 / 192 : ℚ) : ℝ) ≤ ((2735590463093 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2801 : ((52345 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((2801 / 64 : ℚ) : ℝ) ∧
    logKernel ((2801 / 64 : ℚ) : ℝ) ≤ ((209385 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2801
  constructor
  · exact (show ((52345 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((1367795231545 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2801 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((2735590463093 / 18446744073709551616 : ℚ) : ℝ) ≤ ((209385 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2802 : ((1346589532009 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((1401 / 32 : ℚ) : ℝ) ∧
    heightZ ((1401 / 32 : ℚ) : ℝ) ≤ ((2693179064021 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((1346589532009 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((1401 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1339 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1401 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1339 / 96 : ℚ) : ℝ) ≤ ((2693179064021 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2802 : ((101469 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((1401 / 32 : ℚ) : ℝ) ∧
    logKernel ((1401 / 32 : ℚ) : ℝ) ≤ ((202943 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2802
  constructor
  · exact (show ((101469 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((1346589532009 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1401 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((2693179064021 / 18446744073709551616 : ℚ) : ℝ) ≤ ((202943 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2803 : ((2651425192743 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2803 / 64 : ℚ) : ℝ) ∧
    heightZ ((2803 / 64 : ℚ) : ℝ) ≤ ((1325712596373 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((2651425192743 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2803 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2681 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2803 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2681 / 192 : ℚ) : ℝ) ≤ ((1325712596373 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2803 : ((98347 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2803 / 64 : ℚ) : ℝ) ∧
    logKernel ((2803 / 64 : ℚ) : ℝ) ≤ ((196699 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2803
  constructor
  · exact (show ((98347 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((2651425192743 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2803 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1325712596373 / 9223372036854775808 : ℚ) : ℝ) ≤ ((196699 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2804 : ((1305159327621 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((701 / 16 : ℚ) : ℝ) ∧
    heightZ ((701 / 16 : ℚ) : ℝ) ≤ ((2610318655245 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((1305159327621 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((701 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-671 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((701 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-671 / 48 : ℚ) : ℝ) ≤ ((2610318655245 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2804 : ((190643 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((701 / 16 : ℚ) : ℝ) ∧
    logKernel ((701 / 16 : ℚ) : ℝ) ≤ ((23831 / 9007199254740992 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2804
  constructor
  · exact (show ((190643 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((1305159327621 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((701 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((2610318655245 / 18446744073709551616 : ℚ) : ℝ) ≤ ((23831 / 9007199254740992 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2805 : ((2569849415535 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2805 / 64 : ℚ) : ℝ) ∧
    heightZ ((2805 / 64 : ℚ) : ℝ) ≤ ((1284924707769 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((2569849415535 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2805 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2687 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2805 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2687 / 192 : ℚ) : ℝ) ≤ ((1284924707769 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2805 : ((184777 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2805 / 64 : ℚ) : ℝ) ∧
    logKernel ((2805 / 64 : ℚ) : ℝ) ≤ ((92391 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2805
  constructor
  · exact (show ((184777 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((2569849415535 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2805 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1284924707769 / 9223372036854775808 : ℚ) : ℝ) ≤ ((92391 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2806 : ((1265003796617 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((1403 / 32 : ℚ) : ℝ) ∧
    heightZ ((1403 / 32 : ℚ) : ℝ) ≤ ((2530007593237 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((1265003796617 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((1403 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1345 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1403 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1345 / 96 : ℚ) : ℝ) ≤ ((2530007593237 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2806 : ((44773 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((1403 / 32 : ℚ) : ℝ) ∧
    logKernel ((1403 / 32 : ℚ) : ℝ) ≤ ((179097 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2806
  constructor
  · exact (show ((44773 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((1265003796617 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1403 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((2530007593237 / 18446744073709551616 : ℚ) : ℝ) ≤ ((179097 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2807 : ((155673966321 / 1152921504606846976 : ℚ) : ℝ) ≤ heightZ ((2807 / 64 : ℚ) : ℝ) ∧
    heightZ ((2807 / 64 : ℚ) : ℝ) ≤ ((2490783461139 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((155673966321 / 1152921504606846976 : ℚ) : ℝ) ≤ Real.exp (-((2807 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2693 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2807 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2693 / 192 : ℚ) : ℝ) ≤ ((2490783461139 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2807 : ((86791 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2807 / 64 : ℚ) : ℝ) ∧
    logKernel ((2807 / 64 : ℚ) : ℝ) ≤ ((173587 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2807
  constructor
  · exact (show ((86791 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((155673966321 / 1152921504606846976 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2807 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((2490783461139 / 18446744073709551616 : ℚ) : ℝ) ≤ ((173587 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2808 : ((306520930355 / 2305843009213693952 : ℚ) : ℝ) ≤ heightZ ((351 / 8 : ℚ) : ℝ) ∧
    heightZ ((351 / 8 : ℚ) : ℝ) ≤ ((2452167442843 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((306520930355 / 2305843009213693952 : ℚ) : ℝ) ≤ Real.exp (-((351 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-337 / 24 : ℚ) : ℝ) ∧
      Real.exp (-((351 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-337 / 24 : ℚ) : ℝ) ≤ ((2452167442843 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2808 : ((168241 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((351 / 8 : ℚ) : ℝ) ∧
    logKernel ((351 / 8 : ℚ) : ℝ) ≤ ((84123 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2808
  constructor
  · exact (show ((168241 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((306520930355 / 2305843009213693952 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((351 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((2452167442843 / 18446744073709551616 : ℚ) : ℝ) ≤ ((84123 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2809 : ((2414150110417 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2809 / 64 : ℚ) : ℝ) ∧
    heightZ ((2809 / 64 : ℚ) : ℝ) ≤ ((603537527605 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((2414150110417 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2809 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2699 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2809 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2699 / 192 : ℚ) : ℝ) ≤ ((603537527605 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2809 : ((163065 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2809 / 64 : ℚ) : ℝ) ∧
    logKernel ((2809 / 64 : ℚ) : ℝ) ≤ ((81535 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2809
  constructor
  · exact (show ((163065 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((2414150110417 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2809 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((603537527605 / 4611686018427387904 : ℚ) : ℝ) ≤ ((81535 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2810 : ((2376722182101 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1405 / 32 : ℚ) : ℝ) ∧
    heightZ ((1405 / 32 : ℚ) : ℝ) ≤ ((297090272763 / 2305843009213693952 : ℚ) : ℝ) := by
  have h : ((2376722182101 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1405 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1351 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1405 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1351 / 96 : ℚ) : ℝ) ≤ ((297090272763 / 2305843009213693952 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2810 : ((4939 / 2251799813685248 : ℚ) : ℝ) ≤ logKernel ((1405 / 32 : ℚ) : ℝ) ∧
    logKernel ((1405 / 32 : ℚ) : ℝ) ≤ ((158053 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2810
  constructor
  · exact (show ((4939 / 2251799813685248 : ℚ) : ℝ) ≤ zKernel ((2376722182101 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1405 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((297090272763 / 2305843009213693952 : ℚ) : ℝ) ≤ ((158053 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2811 : ((2339874520031 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2811 / 64 : ℚ) : ℝ) ∧
    heightZ ((2811 / 64 : ℚ) : ℝ) ≤ ((1169937260017 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((2339874520031 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2811 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2705 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2811 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2705 / 192 : ℚ) : ℝ) ≤ ((1169937260017 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2811 : ((153185 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2811 / 64 : ℚ) : ℝ) ∧
    logKernel ((2811 / 64 : ℚ) : ℝ) ≤ ((76595 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2811
  constructor
  · exact (show ((153185 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((2339874520031 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2811 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1169937260017 / 9223372036854775808 : ℚ) : ℝ) ≤ ((76595 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2812 : ((1151799064005 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((703 / 16 : ℚ) : ℝ) ∧
    heightZ ((703 / 16 : ℚ) : ℝ) ≤ ((2303598128013 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((1151799064005 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((703 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-677 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((703 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-677 / 48 : ℚ) : ℝ) ≤ ((2303598128013 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2812 : ((18559 / 9007199254740992 : ℚ) : ℝ) ≤ logKernel ((703 / 16 : ℚ) : ℝ) ∧
    logKernel ((703 / 16 : ℚ) : ℝ) ≤ ((148477 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2812
  constructor
  · exact (show ((18559 / 9007199254740992 : ℚ) : ℝ) ≤ zKernel ((1151799064005 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((703 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((2303598128013 / 18446744073709551616 : ℚ) : ℝ) ≤ ((148477 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2813 : ((1133942074659 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2813 / 64 : ℚ) : ℝ) ∧
    heightZ ((2813 / 64 : ℚ) : ℝ) ≤ ((2267884149321 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((1133942074659 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2813 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2711 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2813 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2711 / 192 : ℚ) : ℝ) ≤ ((2267884149321 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2813 : ((4497 / 2251799813685248 : ℚ) : ℝ) ≤ logKernel ((2813 / 64 : ℚ) : ℝ) ∧
    logKernel ((2813 / 64 : ℚ) : ℝ) ≤ ((143909 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2813
  constructor
  · exact (show ((4497 / 2251799813685248 : ℚ) : ℝ) ≤ zKernel ((1133942074659 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2813 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((2267884149321 / 18446744073709551616 : ℚ) : ℝ) ≤ ((143909 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2814 : ((2232723864545 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1407 / 32 : ℚ) : ℝ) ∧
    heightZ ((1407 / 32 : ℚ) : ℝ) ≤ ((558180966137 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((2232723864545 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1407 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1357 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1407 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1357 / 96 : ℚ) : ℝ) ≤ ((558180966137 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2814 : ((34869 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((1407 / 32 : ℚ) : ℝ) ∧
    logKernel ((1407 / 32 : ℚ) : ℝ) ≤ ((139481 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2814
  constructor
  · exact (show ((34869 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((2232723864545 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1407 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((558180966137 / 4611686018427387904 : ℚ) : ℝ) ≤ ((139481 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2815 : ((2198108689461 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2815 / 64 : ℚ) : ℝ) ∧
    heightZ ((2815 / 64 : ℚ) : ℝ) ≤ ((274763586183 / 2305843009213693952 : ℚ) : ℝ) := by
  have h : ((2198108689461 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2815 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2717 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2815 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2717 / 192 : ℚ) : ℝ) ≤ ((274763586183 / 2305843009213693952 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2815 : ((135185 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2815 / 64 : ℚ) : ℝ) ∧
    logKernel ((2815 / 64 : ℚ) : ℝ) ≤ ((67595 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2815
  constructor
  · exact (show ((135185 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((2198108689461 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2815 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((274763586183 / 2305843009213693952 : ℚ) : ℝ) ≤ ((67595 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2816 : ((2164030172925 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((44 / 1 : ℚ) : ℝ) ∧
    heightZ ((44 / 1 : ℚ) : ℝ) ≤ ((8453242863 / 72057594037927936 : ℚ) : ℝ) := by
  have h : ((2164030172925 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((44 / 1 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-85 / 6 : ℚ) : ℝ) ∧
      Real.exp (-((44 / 1 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-85 / 6 : ℚ) : ℝ) ≤ ((8453242863 / 72057594037927936 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2816 : ((65513 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((44 / 1 : ℚ) : ℝ) ∧
    logKernel ((44 / 1 : ℚ) : ℝ) ≤ ((131031 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2816
  constructor
  · exact (show ((65513 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((2164030172925 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((44 / 1 : ℚ) : ℝ)) hh).trans
      (show zKernel ((8453242863 / 72057594037927936 : ℚ) : ℝ) ≤ ((131031 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2817 : ((2130479994817 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2817 / 64 : ℚ) : ℝ) ∧
    heightZ ((2817 / 64 : ℚ) : ℝ) ≤ ((532619998705 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((2130479994817 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2817 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2723 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2817 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2723 / 192 : ℚ) : ℝ) ≤ ((532619998705 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2817 : ((126995 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2817 / 64 : ℚ) : ℝ) ∧
    logKernel ((2817 / 64 : ℚ) : ℝ) ≤ ((15875 / 9007199254740992 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2817
  constructor
  · exact (show ((126995 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((2130479994817 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2817 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((532619998705 / 4611686018427387904 : ℚ) : ℝ) ≤ ((15875 / 9007199254740992 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2818 : ((262181245501 / 2305843009213693952 : ℚ) : ℝ) ≤ heightZ ((1409 / 32 : ℚ) : ℝ) ∧
    heightZ ((1409 / 32 : ℚ) : ℝ) ≤ ((2097449964011 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((262181245501 / 2305843009213693952 : ℚ) : ℝ) ≤ Real.exp (-((1409 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1363 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1409 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1363 / 96 : ℚ) : ℝ) ≤ ((2097449964011 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2818 : ((123087 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1409 / 32 : ℚ) : ℝ) ∧
    logKernel ((1409 / 32 : ℚ) : ℝ) ≤ ((30773 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2818
  constructor
  · exact (show ((123087 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((262181245501 / 2305843009213693952 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1409 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((2097449964011 / 18446744073709551616 : ℚ) : ℝ) ≤ ((30773 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2819 : ((2064932016363 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2819 / 64 : ℚ) : ℝ) ∧
    heightZ ((2819 / 64 : ℚ) : ℝ) ≤ ((1032466008183 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((2064932016363 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2819 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2729 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2819 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2729 / 192 : ℚ) : ℝ) ≤ ((1032466008183 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2819 : ((29825 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((2819 / 64 : ℚ) : ℝ) ∧
    logKernel ((2819 / 64 : ℚ) : ℝ) ≤ ((119305 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2819
  constructor
  · exact (show ((29825 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((2064932016363 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2819 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1032466008183 / 9223372036854775808 : ℚ) : ℝ) ≤ ((119305 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2820 : ((63528694149 / 576460752303423488 : ℚ) : ℝ) ≤ heightZ ((705 / 16 : ℚ) : ℝ) ∧
    heightZ ((705 / 16 : ℚ) : ℝ) ≤ ((2032918212771 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((63528694149 / 576460752303423488 : ℚ) : ℝ) ≤ Real.exp (-((705 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-683 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((705 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-683 / 48 : ℚ) : ℝ) ≤ ((2032918212771 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2820 : ((57815 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((705 / 16 : ℚ) : ℝ) ∧
    logKernel ((705 / 16 : ℚ) : ℝ) ≤ ((115635 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2820
  constructor
  · exact (show ((57815 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((63528694149 / 576460752303423488 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((705 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((2032918212771 / 18446744073709551616 : ℚ) : ℝ) ≤ ((115635 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2821 : ((1000700368597 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2821 / 64 : ℚ) : ℝ) ∧
    heightZ ((2821 / 64 : ℚ) : ℝ) ≤ ((2001400737197 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((1000700368597 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2821 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2735 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2821 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2735 / 192 : ℚ) : ℝ) ≤ ((2001400737197 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2821 : ((14009 / 9007199254740992 : ℚ) : ℝ) ≤ logKernel ((2821 / 64 : ℚ) : ℝ) ∧
    logKernel ((2821 / 64 : ℚ) : ℝ) ≤ ((112077 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2821
  constructor
  · exact (show ((14009 / 9007199254740992 : ℚ) : ℝ) ≤ zKernel ((1000700368597 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2821 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((2001400737197 / 18446744073709551616 : ℚ) : ℝ) ≤ ((112077 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2822 : ((1970371894787 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1411 / 32 : ℚ) : ℝ) ∧
    heightZ ((1411 / 32 : ℚ) : ℝ) ≤ ((985185947395 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((1970371894787 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1411 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1369 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1411 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1369 / 96 : ℚ) : ℝ) ≤ ((985185947395 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2822 : ((6789 / 4503599627370496 : ℚ) : ℝ) ≤ logKernel ((1411 / 32 : ℚ) : ℝ) ∧
    logKernel ((1411 / 32 : ℚ) : ℝ) ≤ ((108629 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2822
  constructor
  · exact (show ((6789 / 4503599627370496 : ℚ) : ℝ) ≤ zKernel ((1970371894787 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1411 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((985185947395 / 9223372036854775808 : ℚ) : ℝ) ≤ ((108629 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2823 : ((969912054997 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2823 / 64 : ℚ) : ℝ) ∧
    heightZ ((2823 / 64 : ℚ) : ℝ) ≤ ((1939824109997 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((969912054997 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2823 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2741 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2823 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2741 / 192 : ℚ) : ℝ) ≤ ((1939824109997 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2823 : ((52641 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2823 / 64 : ℚ) : ℝ) ∧
    logKernel ((2823 / 64 : ℚ) : ℝ) ≤ ((105287 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2823
  constructor
  · exact (show ((52641 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((969912054997 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2823 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1939824109997 / 18446744073709551616 : ℚ) : ℝ) ≤ ((105287 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2824 : ((954874962353 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((353 / 8 : ℚ) : ℝ) ∧
    heightZ ((353 / 8 : ℚ) : ℝ) ≤ ((1909749924709 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((954874962353 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((353 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-343 / 24 : ℚ) : ℝ) ∧
      Real.exp (-((353 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-343 / 24 : ℚ) : ℝ) ≤ ((1909749924709 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2824 : ((51021 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((353 / 8 : ℚ) : ℝ) ∧
    logKernel ((353 / 8 : ℚ) : ℝ) ≤ ((102047 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2824
  constructor
  · exact (show ((51021 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((954874962353 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((353 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1909749924709 / 18446744073709551616 : ℚ) : ℝ) ≤ ((102047 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2825 : ((470035499111 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((2825 / 64 : ℚ) : ℝ) ∧
    heightZ ((2825 / 64 : ℚ) : ℝ) ≤ ((1880141996447 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((470035499111 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((2825 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2747 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2825 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2747 / 192 : ℚ) : ℝ) ≤ ((1880141996447 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2825 : ((98903 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2825 / 64 : ℚ) : ℝ) ∧
    logKernel ((2825 / 64 : ℚ) : ℝ) ≤ ((24727 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2825
  constructor
  · exact (show ((98903 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((470035499111 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2825 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1880141996447 / 18446744073709551616 : ℚ) : ℝ) ≤ ((24727 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2826 : ((1850993096563 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1413 / 32 : ℚ) : ℝ) ∧
    heightZ ((1413 / 32 : ℚ) : ℝ) ≤ ((925496548283 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((1850993096563 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1413 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1375 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1413 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1375 / 96 : ℚ) : ℝ) ≤ ((925496548283 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2826 : ((23965 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((1413 / 32 : ℚ) : ℝ) ∧
    logKernel ((1413 / 32 : ℚ) : ℝ) ≤ ((95865 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2826
  constructor
  · exact (show ((23965 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((1850993096563 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1413 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((925496548283 / 9223372036854775808 : ℚ) : ℝ) ≤ ((95865 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2827 : ((227787013561 / 2305843009213693952 : ℚ) : ℝ) ≤ heightZ ((2827 / 64 : ℚ) : ℝ) ∧
    heightZ ((2827 / 64 : ℚ) : ℝ) ≤ ((1822296108491 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((227787013561 / 2305843009213693952 : ℚ) : ℝ) ≤ Real.exp (-((2827 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2753 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2827 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2753 / 192 : ℚ) : ℝ) ≤ ((1822296108491 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2827 : ((46455 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2827 / 64 : ℚ) : ℝ) ∧
    logKernel ((2827 / 64 : ℚ) : ℝ) ≤ ((92915 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2827
  constructor
  · exact (show ((46455 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((227787013561 / 2305843009213693952 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2827 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1822296108491 / 18446744073709551616 : ℚ) : ℝ) ≤ ((92915 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2828 : ((224255503247 / 2305843009213693952 : ℚ) : ℝ) ≤ heightZ ((707 / 16 : ℚ) : ℝ) ∧
    heightZ ((707 / 16 : ℚ) : ℝ) ≤ ((1794044025979 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((224255503247 / 2305843009213693952 : ℚ) : ℝ) ≤ Real.exp (-((707 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-689 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((707 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-689 / 48 : ℚ) : ℝ) ≤ ((1794044025979 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2828 : ((22513 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((707 / 16 : ℚ) : ℝ) ∧
    logKernel ((707 / 16 : ℚ) : ℝ) ≤ ((90057 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2828
  constructor
  · exact (show ((22513 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((224255503247 / 2305843009213693952 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((707 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1794044025979 / 18446744073709551616 : ℚ) : ℝ) ≤ ((90057 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2829 : ((441557487851 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((2829 / 64 : ℚ) : ℝ) ∧
    heightZ ((2829 / 64 : ℚ) : ℝ) ≤ ((1766229951407 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((441557487851 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((2829 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2759 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2829 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2759 / 192 : ℚ) : ℝ) ≤ ((1766229951407 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2829 : ((87281 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2829 / 64 : ℚ) : ℝ) ∧
    logKernel ((2829 / 64 : ℚ) : ℝ) ≤ ((43643 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2829
  constructor
  · exact (show ((87281 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((441557487851 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2829 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1766229951407 / 18446744073709551616 : ℚ) : ℝ) ≤ ((43643 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem log_height_bounds_960 : ((272320466047855547 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1401 / 32 : ℚ) : ℝ) ∧
    Real.log ((1401 / 32 : ℚ) : ℝ) ≤ ((136160233023927775 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((272320466047855547 / 72057594037927936 : ℚ) : ℝ) ≤ ((1401 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1401 / 32 : ℚ) : ℝ) ≤ Real.exp ((136160233023927775 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_960 : heightPower (960 : Fin 988) ≤ ((4340296471271917 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_960
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_960 : heightFactor (960 : Fin 988) ≤ ((16533429 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_960
  obtain ⟨hpl, hph⟩ := kernel_bounds_2801
  obtain ⟨hcl, hch⟩ := kernel_bounds_2802
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2802
  have h : (((1962801 / 512 : ℚ) : ℝ) * (logKernel ((2801 / 64 : ℚ) : ℝ) - logKernel ((1401 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1401 / 32 : ℚ) : ℝ) + Real.log ((1401 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((16533429 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_961 : ((34043272243261269 / 9007199254740992 : ℚ) : ℝ) ≤ Real.log ((2803 / 64 : ℚ) : ℝ) ∧
    Real.log ((2803 / 64 : ℚ) : ℝ) ≤ ((272346177946090155 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((34043272243261269 / 9007199254740992 : ℚ) : ℝ) ≤ ((2803 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2803 / 64 : ℚ) : ℝ) ≤ Real.exp ((272346177946090155 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_961 : heightPower (961 : Fin 988) ≤ ((1086198738721375 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_961
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_961 : heightFactor (961 : Fin 988) ≤ ((8061739 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_961
  obtain ⟨hpl, hph⟩ := kernel_bounds_2802
  obtain ⟨hcl, hch⟩ := kernel_bounds_2803
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2803
  have h : (((7856809 / 2048 : ℚ) : ℝ) * (logKernel ((1401 / 32 : ℚ) : ℝ) - logKernel ((2803 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2803 / 64 : ℚ) : ℝ) + Real.log ((2803 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((8061739 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_962 : ((34046485084120995 / 9007199254740992 : ℚ) : ℝ) ≤ Real.log ((701 / 16 : ℚ) : ℝ) ∧
    Real.log ((701 / 16 : ℚ) : ℝ) ≤ ((272371880672967963 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((34046485084120995 / 9007199254740992 : ℚ) : ℝ) ≤ ((701 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((701 / 16 : ℚ) : ℝ) ≤ Real.exp ((272371880672967963 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_962 : heightPower (962 : Fin 988) ≤ ((4349293402673471 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_962
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_962 : heightFactor (962 : Fin 988) ≤ ((15723727 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_962
  obtain ⟨hpl, hph⟩ := kernel_bounds_2803
  obtain ⟨hcl, hch⟩ := kernel_bounds_2804
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2804
  have h : (((491401 / 128 : ℚ) : ℝ) * (logKernel ((2803 / 64 : ℚ) : ℝ) - logKernel ((701 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((701 / 16 : ℚ) : ℝ) + Real.log ((701 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((15723727 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_963 : ((272397574235029429 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2805 / 64 : ℚ) : ℝ) ∧
    Real.log ((2805 / 64 : ℚ) : ℝ) ≤ ((34049696779378679 / 9007199254740992 : ℚ) : ℝ) := by
  have hl : Real.exp ((272397574235029429 / 72057594037927936 : ℚ) : ℝ) ≤ ((2805 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2805 / 64 : ℚ) : ℝ) ≤ Real.exp ((34049696779378679 / 9007199254740992 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_963 : heightPower (963 : Fin 988) ≤ ((4353791814661377 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_963
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_963 : heightFactor (963 : Fin 988) ≤ ((15333923 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_963
  obtain ⟨hpl, hph⟩ := kernel_bounds_2804
  obtain ⟨hcl, hch⟩ := kernel_bounds_2805
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2805
  have h : (((7868025 / 2048 : ℚ) : ℝ) * (logKernel ((701 / 16 : ℚ) : ℝ) - logKernel ((2805 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2805 / 64 : ℚ) : ℝ) + Real.log ((2805 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((15333923 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_964 : ((34052907329851003 / 9007199254740992 : ℚ) : ℝ) ≤ Real.log ((1403 / 32 : ℚ) : ℝ) ∧
    Real.log ((1403 / 32 : ℚ) : ℝ) ≤ ((272423258638808027 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((34052907329851003 / 9007199254740992 : ℚ) : ℝ) ≤ ((1403 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1403 / 32 : ℚ) : ℝ) ≤ Real.exp ((272423258638808027 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_964 : heightPower (964 : Fin 988) ≤ ((4358290190874741 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_964
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_964 : heightFactor (964 : Fin 988) ≤ ((14953819 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_964
  obtain ⟨hpl, hph⟩ := kernel_bounds_2805
  obtain ⟨hcl, hch⟩ := kernel_bounds_2806
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2806
  have h : (((1968409 / 512 : ℚ) : ℝ) * (logKernel ((2805 / 64 : ℚ) : ℝ) - logKernel ((1403 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1403 / 32 : ℚ) : ℝ) + Real.log ((1403 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((14953819 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_965 : ((272448933890830223 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2807 / 64 : ℚ) : ℝ) ∧
    Real.log ((2807 / 64 : ℚ) : ℝ) ≤ ((136224466945415113 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((272448933890830223 / 72057594037927936 : ℚ) : ℝ) ≤ ((2807 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2807 / 64 : ℚ) : ℝ) ≤ Real.exp ((136224466945415113 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_965 : heightPower (965 : Fin 988) ≤ ((4362788531339057 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_965
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_965 : heightFactor (965 : Fin 988) ≤ ((14583173 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_965
  obtain ⟨hpl, hph⟩ := kernel_bounds_2806
  obtain ⟨hcl, hch⟩ := kernel_bounds_2807
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2807
  have h : (((7879249 / 2048 : ℚ) : ℝ) * (logKernel ((1403 / 32 : ℚ) : ℝ) - logKernel ((2807 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2807 / 64 : ℚ) : ℝ) + Real.log ((2807 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((14583173 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_966 : ((136237299998807767 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((351 / 8 : ℚ) : ℝ) ∧
    Real.log ((351 / 8 : ℚ) : ℝ) ≤ ((272474599997615537 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((136237299998807767 / 36028797018963968 : ℚ) : ℝ) ≤ ((351 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((351 / 8 : ℚ) : ℝ) ≤ Real.exp ((272474599997615537 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_966 : heightPower (966 : Fin 988) ≤ ((4367286836079791 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_966
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_966 : heightFactor (966 : Fin 988) ≤ ((14221751 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_966
  obtain ⟨hpl, hph⟩ := kernel_bounds_2807
  obtain ⟨hcl, hch⟩ := kernel_bounds_2808
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2808
  have h : (((123201 / 32 : ℚ) : ℝ) * (logKernel ((2807 / 64 : ℚ) : ℝ) - logKernel ((351 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((351 / 8 : ℚ) : ℝ) + Real.log ((351 / 8 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((14221751 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_967 : ((136250128482838249 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2809 / 64 : ℚ) : ℝ) ∧
    Real.log ((2809 / 64 : ℚ) : ℝ) ≤ ((272500256965676501 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((136250128482838249 / 36028797018963968 : ℚ) : ℝ) ≤ ((2809 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2809 / 64 : ℚ) : ℝ) ≤ Real.exp ((272500256965676501 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_967 : heightPower (967 : Fin 988) ≤ ((4371785105122383 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_967
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_967 : heightFactor (967 : Fin 988) ≤ ((6934661 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_967
  obtain ⟨hpl, hph⟩ := kernel_bounds_2808
  obtain ⟨hcl, hch⟩ := kernel_bounds_2809
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2809
  have h : (((7890481 / 2048 : ℚ) : ℝ) * (logKernel ((351 / 8 : ℚ) : ℝ) - logKernel ((2809 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2809 / 64 : ℚ) : ℝ) + Real.log ((2809 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((6934661 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_968 : ((272525904801518703 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1405 / 32 : ℚ) : ℝ) ∧
    Real.log ((1405 / 32 : ℚ) : ℝ) ≤ ((136262952400759353 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((272525904801518703 / 72057594037927936 : ℚ) : ℝ) ≤ ((1405 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1405 / 32 : ℚ) : ℝ) ≤ Real.exp ((136262952400759353 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_968 : heightPower (968 : Fin 988) ≤ ((2188141669246123 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_968
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_968 : heightFactor (968 : Fin 988) ≤ ((6762831 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_968
  obtain ⟨hpl, hph⟩ := kernel_bounds_2809
  obtain ⟨hcl, hch⟩ := kernel_bounds_2810
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2810
  have h : (((1974025 / 512 : ℚ) : ℝ) * (logKernel ((2809 / 64 : ℚ) : ℝ) - logKernel ((1405 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1405 / 32 : ℚ) : ℝ) + Real.log ((1405 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((6762831 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_969 : ((272551543511640793 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2811 / 64 : ℚ) : ℝ) ∧
    Real.log ((2811 / 64 : ℚ) : ℝ) ≤ ((68137885877910199 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((272551543511640793 / 72057594037927936 : ℚ) : ℝ) ≤ ((2811 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2811 / 64 : ℚ) : ℝ) ≤ Real.exp ((68137885877910199 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_969 : heightPower (969 : Fin 988) ≤ ((1095195384053691 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_969
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_969 : heightFactor (969 : Fin 988) ≤ ((13190555 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_969
  obtain ⟨hpl, hph⟩ := kernel_bounds_2810
  obtain ⟨hcl, hch⟩ := kernel_bounds_2811
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2811
  have h : (((7901721 / 2048 : ℚ) : ℝ) * (logKernel ((1405 / 32 : ℚ) : ℝ) - logKernel ((2811 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2811 / 64 : ℚ) : ℝ) + Real.log ((2811 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((13190555 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_970 : ((272577173102534477 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((703 / 16 : ℚ) : ℝ) ∧
    Real.log ((703 / 16 : ℚ) : ℝ) ≤ ((17036073318908405 / 4503599627370496 : ℚ) : ℝ) := by
  have hl : Real.exp ((272577173102534477 / 72057594037927936 : ℚ) : ℝ) ≤ ((703 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((703 / 16 : ℚ) : ℝ) ≤ Real.exp ((17036073318908405 / 4503599627370496 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_970 : heightPower (970 : Fin 988) ≤ ((4385279698315297 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_970
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_970 : heightFactor (970 : Fin 988) ≤ ((12863787 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_970
  obtain ⟨hpl, hph⟩ := kernel_bounds_2811
  obtain ⟨hcl, hch⟩ := kernel_bounds_2812
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2812
  have h : (((494209 / 128 : ℚ) : ℝ) * (logKernel ((2811 / 64 : ℚ) : ℝ) - logKernel ((703 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((703 / 16 : ℚ) : ℝ) + Real.log ((703 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((12863787 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_971 : ((68150698395171135 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((2813 / 64 : ℚ) : ℝ) ∧
    Real.log ((2813 / 64 : ℚ) : ℝ) ≤ ((272602793580684543 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((68150698395171135 / 18014398509481984 : ℚ) : ℝ) ≤ ((2813 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2813 / 64 : ℚ) : ℝ) ≤ Real.exp ((272602793580684543 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_971 : heightPower (971 : Fin 988) ≤ ((2194888912409587 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_971
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_971 : heightFactor (971 : Fin 988) ≤ ((12545151 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_971
  obtain ⟨hpl, hph⟩ := kernel_bounds_2812
  obtain ⟨hcl, hch⟩ := kernel_bounds_2813
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2813
  have h : (((7912969 / 2048 : ℚ) : ℝ) * (logKernel ((703 / 16 : ℚ) : ℝ) - logKernel ((2813 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2813 / 64 : ℚ) : ℝ) + Real.log ((2813 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((12545151 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_972 : ((272628404952568853 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1407 / 32 : ℚ) : ℝ) ∧
    Real.log ((1407 / 32 : ℚ) : ℝ) ≤ ((34078550619071107 / 9007199254740992 : ℚ) : ℝ) := by
  have hl : Real.exp ((272628404952568853 / 72057594037927936 : ℚ) : ℝ) ≤ ((1407 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1407 / 32 : ℚ) : ℝ) ≤ Real.exp ((34078550619071107 / 9007199254740992 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_972 : heightPower (972 : Fin 988) ≤ ((2197137957875851 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_972
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_972 : heightFactor (972 : Fin 988) ≤ ((3058611 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_972
  obtain ⟨hpl, hph⟩ := kernel_bounds_2813
  obtain ⟨hcl, hch⟩ := kernel_bounds_2814
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2814
  have h : (((1979649 / 512 : ℚ) : ℝ) * (logKernel ((2813 / 64 : ℚ) : ℝ) - logKernel ((1407 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1407 / 32 : ℚ) : ℝ) + Real.log ((1407 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((3058611 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_973 : ((68163501806164595 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((2815 / 64 : ℚ) : ℝ) ∧
    Real.log ((2815 / 64 : ℚ) : ℝ) ≤ ((272654007224658383 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((68163501806164595 / 18014398509481984 : ℚ) : ℝ) ≤ ((2815 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2815 / 64 : ℚ) : ℝ) ≤ Real.exp ((272654007224658383 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_973 : heightPower (973 : Fin 988) ≤ ((4398773971138155 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_973
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_973 : heightFactor (973 : Fin 988) ≤ ((11931469 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_973
  obtain ⟨hpl, hph⟩ := kernel_bounds_2814
  obtain ⟨hcl, hch⟩ := kernel_bounds_2815
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2815
  have h : (((7924225 / 2048 : ℚ) : ℝ) * (logKernel ((1407 / 32 : ℚ) : ℝ) - logKernel ((2815 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2815 / 64 : ℚ) : ℝ) + Real.log ((2815 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((11931469 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_974 : ((272679600403417193 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((44 / 1 : ℚ) : ℝ) ∧
    Real.log ((44 / 1 : ℚ) : ℝ) ≤ ((68169900100854299 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((272679600403417193 / 72057594037927936 : ℚ) : ℝ) ≤ ((44 / 1 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((44 / 1 : ℚ) : ℝ) ≤ Real.exp ((68169900100854299 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_974 : heightPower (974 : Fin 988) ≤ ((2201635995501893 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_974
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_974 : heightFactor (974 : Fin 988) ≤ ((5818017 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_974
  obtain ⟨hpl, hph⟩ := kernel_bounds_2815
  obtain ⟨hcl, hch⟩ := kernel_bounds_2816
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2816
  have h : (((3872 / 1 : ℚ) : ℝ) * (logKernel ((2815 / 64 : ℚ) : ℝ) - logKernel ((44 / 1 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((44 / 1 : ℚ) : ℝ) + Real.log ((44 / 1 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((5818017 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_975 : ((272705184495302475 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2817 / 64 : ℚ) : ℝ) ∧
    Real.log ((2817 / 64 : ℚ) : ℝ) ≤ ((136352592247651239 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((272705184495302475 / 72057594037927936 : ℚ) : ℝ) ≤ ((2817 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2817 / 64 : ℚ) : ℝ) ≤ Real.exp ((136352592247651239 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_975 : heightPower (975 : Fin 988) ≤ ((4407769975373817 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_975
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_975 : heightFactor (975 : Fin 988) ≤ ((709247 / 17592186044416 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_975
  obtain ⟨hpl, hph⟩ := kernel_bounds_2816
  obtain ⟨hcl, hch⟩ := kernel_bounds_2817
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2817
  have h : (((7935489 / 2048 : ℚ) : ℝ) * (logKernel ((44 / 1 : ℚ) : ℝ) - logKernel ((2817 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2817 / 64 : ℚ) : ℝ) + Real.log ((2817 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((709247 / 17592186044416 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_976 : ((136365379753382269 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((1409 / 32 : ℚ) : ℝ) ∧
    Real.log ((1409 / 32 : ℚ) : ℝ) ≤ ((272730759506764541 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((136365379753382269 / 36028797018963968 : ℚ) : ℝ) ≤ ((1409 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1409 / 32 : ℚ) : ℝ) ≤ Real.exp ((272730759506764541 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_976 : heightPower (976 : Fin 988) ≤ ((1103066981068361 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_976
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_976 : heightFactor (976 : Fin 988) ≤ ((11067039 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_976
  obtain ⟨hpl, hph⟩ := kernel_bounds_2817
  obtain ⟨hcl, hch⟩ := kernel_bounds_2818
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2818
  have h : (((1985281 / 512 : ℚ) : ℝ) * (logKernel ((2817 / 64 : ℚ) : ℝ) - logKernel ((1409 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1409 / 32 : ℚ) : ℝ) + Real.log ((1409 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((11067039 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_977 : ((272756325444246825 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2819 / 64 : ℚ) : ℝ) ∧
    Real.log ((2819 / 64 : ℚ) : ℝ) ≤ ((68189081361061707 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((272756325444246825 / 72057594037927936 : ℚ) : ℝ) ≤ ((2819 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2819 / 64 : ℚ) : ℝ) ≤ Real.exp ((68189081361061707 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_977 : heightPower (977 : Fin 988) ≤ ((4416765837727839 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_977
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_977 : heightFactor (977 : Fin 988) ≤ ((10793117 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_977
  obtain ⟨hpl, hph⟩ := kernel_bounds_2818
  obtain ⟨hcl, hch⟩ := kernel_bounds_2819
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2819
  have h : (((7946761 / 2048 : ℚ) : ℝ) * (logKernel ((1409 / 32 : ℚ) : ℝ) - logKernel ((2819 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2819 / 64 : ℚ) : ℝ) + Real.log ((2819 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((10793117 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_978 : ((272781882314185923 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((705 / 16 : ℚ) : ℝ) ∧
    Real.log ((705 / 16 : ℚ) : ℝ) ≤ ((136390941157092963 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((272781882314185923 / 72057594037927936 : ℚ) : ℝ) ≤ ((705 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((705 / 16 : ℚ) : ℝ) ≤ Real.exp ((136390941157092963 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_978 : heightPower (978 : Fin 988) ≤ ((2210631857881071 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_978
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_978 : heightFactor (978 : Fin 988) ≤ ((2631503 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_978
  obtain ⟨hpl, hph⟩ := kernel_bounds_2819
  obtain ⟨hcl, hch⟩ := kernel_bounds_2820
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2820
  have h : (((497025 / 128 : ℚ) : ℝ) * (logKernel ((2819 / 64 : ℚ) : ℝ) - logKernel ((705 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((705 / 16 : ℚ) : ℝ) + Real.log ((705 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((2631503 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_979 : ((34100928765376447 / 9007199254740992 : ℚ) : ℝ) ≤ Real.log ((2821 / 64 : ℚ) : ℝ) ∧
    Real.log ((2821 / 64 : ℚ) : ℝ) ≤ ((272807430123011579 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((34100928765376447 / 9007199254740992 : ℚ) : ℝ) ≤ ((2821 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2821 / 64 : ℚ) : ℝ) ≤ Real.exp ((272807430123011579 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_979 : heightPower (979 : Fin 988) ≤ ((4425761558401471 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_979
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_979 : heightFactor (979 : Fin 988) ≤ ((10265555 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_979
  obtain ⟨hpl, hph⟩ := kernel_bounds_2820
  obtain ⟨hcl, hch⟩ := kernel_bounds_2821
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2821
  have h : (((7958041 / 2048 : ℚ) : ℝ) * (logKernel ((705 / 16 : ℚ) : ℝ) - logKernel ((2821 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2821 / 64 : ℚ) : ℝ) + Real.log ((2821 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((10265555 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_980 : ((4263015138705417 / 1125899906842624 : ℚ) : ℝ) ≤ Real.log ((1411 / 32 : ℚ) : ℝ) ∧
    Real.log ((1411 / 32 : ℚ) : ℝ) ≤ ((272832968877146691 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((4263015138705417 / 1125899906842624 : ℚ) : ℝ) ≤ ((1411 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1411 / 32 : ℚ) : ℝ) ≤ Real.exp ((272832968877146691 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_980 : heightPower (980 : Fin 988) ≤ ((1107564841417729 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_980
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_980 : heightFactor (980 : Fin 988) ≤ ((2502895 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_980
  obtain ⟨hpl, hph⟩ := kernel_bounds_2821
  obtain ⟨hcl, hch⟩ := kernel_bounds_2822
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2822
  have h : (((1990921 / 512 : ℚ) : ℝ) * (logKernel ((2821 / 64 : ℚ) : ℝ) - logKernel ((1411 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1411 / 32 : ℚ) : ℝ) + Real.log ((1411 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((2502895 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_981 : ((272858498583007337 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2823 / 64 : ℚ) : ℝ) ∧
    Real.log ((2823 / 64 : ℚ) : ℝ) ≤ ((68214624645751835 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((272858498583007337 / 72057594037927936 : ℚ) : ℝ) ≤ ((2823 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2823 / 64 : ℚ) : ℝ) ≤ Real.exp ((68214624645751835 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_981 : heightPower (981 : Fin 988) ≤ ((2217378568797769 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_981
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_981 : heightFactor (981 : Fin 988) ≤ ((9763927 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_981
  obtain ⟨hpl, hph⟩ := kernel_bounds_2822
  obtain ⟨hcl, hch⟩ := kernel_bounds_2823
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2823
  have h : (((7969329 / 2048 : ℚ) : ℝ) * (logKernel ((1411 / 32 : ℚ) : ℝ) - logKernel ((2823 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2823 / 64 : ℚ) : ℝ) + Real.log ((2823 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((9763927 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_982 : ((136442009623501393 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((353 / 8 : ℚ) : ℝ) ∧
    Real.log ((353 / 8 : ℚ) : ℝ) ≤ ((272884019247002789 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((136442009623501393 / 36028797018963968 : ℚ) : ℝ) ≤ ((353 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((353 / 8 : ℚ) : ℝ) ≤ Real.exp ((272884019247002789 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_982 : heightPower (982 : Fin 988) ≤ ((2219627437100187 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_982
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_982 : heightFactor (982 : Fin 988) ≤ ((9522437 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_982
  obtain ⟨hpl, hph⟩ := kernel_bounds_2823
  obtain ⟨hcl, hch⟩ := kernel_bounds_2824
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2824
  have h : (((124609 / 32 : ℚ) : ℝ) * (logKernel ((2823 / 64 : ℚ) : ℝ) - logKernel ((353 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((353 / 8 : ℚ) : ℝ) + Real.log ((353 / 8 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((9522437 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_983 : ((2132105709965121 / 562949953421312 : ℚ) : ℝ) ≤ Real.log ((2825 / 64 : ℚ) : ℝ) ∧
    Real.log ((2825 / 64 : ℚ) : ℝ) ≤ ((272909530875535491 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((2132105709965121 / 562949953421312 : ℚ) : ℝ) ≤ ((2825 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2825 / 64 : ℚ) : ℝ) ≤ Real.exp ((272909530875535491 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_983 : heightPower (983 : Fin 988) ≤ ((2221876287755217 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_983
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_983 : heightFactor (983 : Fin 988) ≤ ((9286957 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_983
  obtain ⟨hpl, hph⟩ := kernel_bounds_2824
  obtain ⟨hcl, hch⟩ := kernel_bounds_2825
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2825
  have h : (((7980625 / 2048 : ℚ) : ℝ) * (logKernel ((353 / 8 : ℚ) : ℝ) - logKernel ((2825 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2825 / 64 : ℚ) : ℝ) + Real.log ((2825 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((9286957 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_984 : ((272935033475001099 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1413 / 32 : ℚ) : ℝ) ∧
    Real.log ((1413 / 32 : ℚ) : ℝ) ≤ ((136467516737500551 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((272935033475001099 / 72057594037927936 : ℚ) : ℝ) ≤ ((1413 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1413 / 32 : ℚ) : ℝ) ≤ Real.exp ((136467516737500551 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_984 : heightPower (984 : Fin 988) ≤ ((4448250241550701 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_984
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_984 : heightFactor (984 : Fin 988) ≤ ((4528669 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_984
  obtain ⟨hpl, hph⟩ := kernel_bounds_2825
  obtain ⟨hcl, hch⟩ := kernel_bounds_2826
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2826
  have h : (((1996569 / 512 : ℚ) : ℝ) * (logKernel ((2825 / 64 : ℚ) : ℝ) - logKernel ((1413 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1413 / 32 : ℚ) : ℝ) + Real.log ((1413 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((4528669 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_985 : ((272960527051788487 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2827 / 64 : ℚ) : ℝ) ∧
    Real.log ((2827 / 64 : ℚ) : ℝ) ≤ ((136480263525894245 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((272960527051788487 / 72057594037927936 : ℚ) : ℝ) ≤ ((2827 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2827 / 64 : ℚ) : ℝ) ≤ Real.exp ((136480263525894245 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_985 : heightPower (985 : Fin 988) ≤ ((2226373936173065 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_985
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_985 : heightFactor (985 : Fin 988) ≤ ((4416717 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_985
  obtain ⟨hpl, hph⟩ := kernel_bounds_2826
  obtain ⟨hcl, hch⟩ := kernel_bounds_2827
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2827
  have h : (((7991929 / 2048 : ℚ) : ℝ) * (logKernel ((1413 / 32 : ℚ) : ℝ) - logKernel ((2827 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2827 / 64 : ℚ) : ℝ) + Real.log ((2827 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((4416717 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_986 : ((272986011612279741 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((707 / 16 : ℚ) : ℝ) ∧
    Real.log ((707 / 16 : ℚ) : ℝ) ≤ ((4265406431441871 / 1125899906842624 : ℚ) : ℝ) := by
  have hl : Real.exp ((272986011612279741 / 72057594037927936 : ℚ) : ℝ) ≤ ((707 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((707 / 16 : ℚ) : ℝ) ≤ Real.exp ((4265406431441871 / 1125899906842624 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_986 : heightPower (986 : Fin 988) ≤ ((4457245467921653 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_986
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_986 : heightFactor (986 : Fin 988) ≤ ((8615103 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_986
  obtain ⟨hpl, hph⟩ := kernel_bounds_2827
  obtain ⟨hcl, hch⟩ := kernel_bounds_2828
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2828
  have h : (((499849 / 128 : ℚ) : ℝ) * (logKernel ((2827 / 64 : ℚ) : ℝ) - logKernel ((707 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((707 / 16 : ℚ) : ℝ) + Real.log ((707 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((8615103 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_987 : ((273011487162850181 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2829 / 64 : ℚ) : ℝ) ∧
    Real.log ((2829 / 64 : ℚ) : ℝ) ≤ ((34126435895356273 / 9007199254740992 : ℚ) : ℝ) := by
  have hl : Real.exp ((273011487162850181 / 72057594037927936 : ℚ) : ℝ) ≤ ((2829 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2829 / 64 : ℚ) : ℝ) ≤ Real.exp ((34126435895356273 / 9007199254740992 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_987 : heightPower (987 : Fin 988) ≤ ((4461743028302173 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_987
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_987 : heightFactor (987 : Fin 988) ≤ ((2105215725 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_987
  obtain ⟨hpl, hph⟩ := kernel_bounds_2828
  obtain ⟨hcl, hch⟩ := kernel_bounds_2829
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2829
  have h : (((8003241 / 2048 : ℚ) : ℝ) * (logKernel ((707 / 16 : ℚ) : ℝ) - logKernel ((2829 / 64 : ℚ) : ℝ)) + ((256103712 / 31 : ℚ) : ℝ) * (heightZ ((2829 / 64 : ℚ) : ℝ)) ^ 2) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2829 / 64 : ℚ) : ℝ) + Real.log ((2829 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((2105215725 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

end LegendreK6.M2Pilot.Enclosures.Height030
