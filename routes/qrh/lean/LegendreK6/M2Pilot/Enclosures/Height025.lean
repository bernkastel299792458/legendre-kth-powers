import LegendreK6.M2PilotDefinitions
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp

/-! Generated proposals: every bound is checked by Lean, not by trusting Arb. -/
namespace LegendreK6.M2Pilot.Enclosures.Height025
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem height_z_bounds_2641 : ((33326314295569 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2641 / 64 : ℚ) : ℝ) ∧
    heightZ ((2641 / 64 : ℚ) : ℝ) ≤ ((8331578573893 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((33326314295569 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2641 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2195 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2641 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2195 / 192 : ℚ) : ℝ) ≤ ((8331578573893 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2641 : ((31075141 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2641 / 64 : ℚ) : ℝ) ∧
    logKernel ((2641 / 64 : ℚ) : ℝ) ≤ ((15537573 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2641
  constructor
  · exact (show ((31075141 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((33326314295569 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2641 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((8331578573893 / 4611686018427387904 : ℚ) : ℝ) ≤ ((15537573 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2642 : ((16404818841255 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((1321 / 32 : ℚ) : ℝ) ∧
    heightZ ((1321 / 32 : ℚ) : ℝ) ≤ ((32809637682513 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((16404818841255 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((1321 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1099 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1321 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1099 / 96 : ℚ) : ℝ) ≤ ((32809637682513 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2642 : ((30119059 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1321 / 32 : ℚ) : ℝ) ∧
    logKernel ((1321 / 32 : ℚ) : ℝ) ≤ ((3764883 / 9007199254740992 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2642
  constructor
  · exact (show ((30119059 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((16404818841255 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1321 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((32809637682513 / 18446744073709551616 : ℚ) : ℝ) ≤ ((3764883 / 9007199254740992 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2643 : ((16150485698935 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2643 / 64 : ℚ) : ℝ) ∧
    heightZ ((2643 / 64 : ℚ) : ℝ) ≤ ((32300971397873 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((16150485698935 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2643 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2201 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2643 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2201 / 192 : ℚ) : ℝ) ≤ ((32300971397873 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2643 : ((29192393 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2643 / 64 : ℚ) : ℝ) ∧
    logKernel ((2643 / 64 : ℚ) : ℝ) ≤ ((14596199 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2643
  constructor
  · exact (show ((29192393 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((16150485698935 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2643 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((32300971397873 / 18446744073709551616 : ℚ) : ℝ) ≤ ((14596199 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2644 : ((3975023906627 / 2305843009213693952 : ℚ) : ℝ) ≤ heightZ ((661 / 16 : ℚ) : ℝ) ∧
    heightZ ((661 / 16 : ℚ) : ℝ) ≤ ((31800191253019 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((3975023906627 / 2305843009213693952 : ℚ) : ℝ) ≤ Real.exp (-((661 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-551 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((661 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-551 / 48 : ℚ) : ℝ) ≤ ((31800191253019 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2644 : ((28294237 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((661 / 16 : ℚ) : ℝ) ∧
    logKernel ((661 / 16 : ℚ) : ℝ) ≤ ((14147121 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2644
  constructor
  · exact (show ((28294237 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((3975023906627 / 2305843009213693952 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((661 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((31800191253019 / 18446744073709551616 : ℚ) : ℝ) ≤ ((14147121 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2645 : ((31307174984685 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2645 / 64 : ℚ) : ℝ) ∧
    heightZ ((2645 / 64 : ℚ) : ℝ) ≤ ((1956698436543 / 1152921504606846976 : ℚ) : ℝ) := by
  have h : ((31307174984685 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2645 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2207 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2645 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2207 / 192 : ℚ) : ℝ) ≤ ((1956698436543 / 1152921504606846976 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2645 : ((27423715 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2645 / 64 : ℚ) : ℝ) ∧
    logKernel ((2645 / 64 : ℚ) : ℝ) ≤ ((3427965 / 9007199254740992 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2645
  constructor
  · exact (show ((27423715 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((31307174984685 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2645 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1956698436543 / 1152921504606846976 : ℚ) : ℝ) ≤ ((3427965 / 9007199254740992 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2646 : ((30821802225127 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1323 / 32 : ℚ) : ℝ) ∧
    heightZ ((1323 / 32 : ℚ) : ℝ) ≤ ((15410901112565 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((30821802225127 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1323 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1105 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1323 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1105 / 96 : ℚ) : ℝ) ≤ ((15410901112565 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2646 : ((3322497 / 9007199254740992 : ℚ) : ℝ) ≤ logKernel ((1323 / 32 : ℚ) : ℝ) ∧
    logKernel ((1323 / 32 : ℚ) : ℝ) ≤ ((26579981 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2646
  constructor
  · exact (show ((3322497 / 9007199254740992 : ℚ) : ℝ) ≤ zKernel ((30821802225127 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1323 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((15410901112565 / 9223372036854775808 : ℚ) : ℝ) ≤ ((26579981 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2647 : ((30343954472723 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2647 / 64 : ℚ) : ℝ) ∧
    heightZ ((2647 / 64 : ℚ) : ℝ) ≤ ((15171977236363 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((30343954472723 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2647 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2213 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2647 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2213 / 192 : ℚ) : ℝ) ≤ ((15171977236363 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2647 : ((6440549 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((2647 / 64 : ℚ) : ℝ) ∧
    logKernel ((2647 / 64 : ℚ) : ℝ) ≤ ((25762201 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2647
  constructor
  · exact (show ((6440549 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((30343954472723 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2647 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((15171977236363 / 9223372036854775808 : ℚ) : ℝ) ≤ ((25762201 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2648 : ((14936757531525 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((331 / 8 : ℚ) : ℝ) ∧
    heightZ ((331 / 8 : ℚ) : ℝ) ≤ ((29873515063053 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((14936757531525 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((331 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-277 / 24 : ℚ) : ℝ) ∧
      Real.exp (-((331 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-277 / 24 : ℚ) : ℝ) ≤ ((29873515063053 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2648 : ((3121197 / 9007199254740992 : ℚ) : ℝ) ≤ logKernel ((331 / 8 : ℚ) : ℝ) ∧
    logKernel ((331 / 8 : ℚ) : ℝ) ≤ ((24969581 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2648
  constructor
  · exact (show ((3121197 / 9007199254740992 : ℚ) : ℝ) ≤ zKernel ((14936757531525 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((331 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((29873515063053 / 18446744073709551616 : ℚ) : ℝ) ≤ ((24969581 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2649 : ((1838148071275 / 1152921504606846976 : ℚ) : ℝ) ≤ heightZ ((2649 / 64 : ℚ) : ℝ) ∧
    heightZ ((2649 / 64 : ℚ) : ℝ) ≤ ((29410369140403 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((1838148071275 / 1152921504606846976 : ℚ) : ℝ) ≤ Real.exp (-((2649 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2219 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2649 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2219 / 192 : ℚ) : ℝ) ≤ ((29410369140403 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2649 : ((24201343 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2649 / 64 : ℚ) : ℝ) ∧
    logKernel ((2649 / 64 : ℚ) : ℝ) ≤ ((6050337 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2649
  constructor
  · exact (show ((24201343 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((1838148071275 / 1152921504606846976 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2649 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((29410369140403 / 18446744073709551616 : ℚ) : ℝ) ≤ ((6050337 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2650 : ((14477201814869 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((1325 / 32 : ℚ) : ℝ) ∧
    heightZ ((1325 / 32 : ℚ) : ℝ) ≤ ((28954403629741 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((14477201814869 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((1325 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1111 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1325 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1111 / 96 : ℚ) : ℝ) ≤ ((28954403629741 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2650 : ((11728373 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((1325 / 32 : ℚ) : ℝ) ∧
    logKernel ((1325 / 32 : ℚ) : ℝ) ≤ ((23456751 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2650
  constructor
  · exact (show ((11728373 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((14477201814869 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1325 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((28954403629741 / 18446744073709551616 : ℚ) : ℝ) ≤ ((23456751 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2651 : ((14252753604547 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2651 / 64 : ℚ) : ℝ) ∧
    heightZ ((2651 / 64 : ℚ) : ℝ) ≤ ((28505507209097 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((14252753604547 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2651 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2225 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2651 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2225 / 192 : ℚ) : ℝ) ≤ ((28505507209097 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2651 : ((11367529 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2651 / 64 : ℚ) : ℝ) ∧
    logKernel ((2651 / 64 : ℚ) : ℝ) ≤ ((22735063 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2651
  constructor
  · exact (show ((11367529 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((14252753604547 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2651 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((28505507209097 / 18446744073709551616 : ℚ) : ℝ) ≤ ((22735063 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2652 : ((28063570282385 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((663 / 16 : ℚ) : ℝ) ∧
    heightZ ((663 / 16 : ℚ) : ℝ) ≤ ((7015892570597 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((28063570282385 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((663 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-557 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((663 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-557 / 48 : ℚ) : ℝ) ≤ ((7015892570597 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2652 : ((11017787 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((663 / 16 : ℚ) : ℝ) ∧
    logKernel ((663 / 16 : ℚ) : ℝ) ≤ ((22035579 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2652
  constructor
  · exact (show ((11017787 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((28063570282385 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((663 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((7015892570597 / 4611686018427387904 : ℚ) : ℝ) ≤ ((22035579 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2653 : ((13814242476329 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2653 / 64 : ℚ) : ℝ) ∧
    heightZ ((2653 / 64 : ℚ) : ℝ) ≤ ((27628484952661 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((13814242476329 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2653 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2231 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2653 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2231 / 192 : ℚ) : ℝ) ≤ ((27628484952661 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2653 : ((10678805 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2653 / 64 : ℚ) : ℝ) ∧
    logKernel ((2653 / 64 : ℚ) : ℝ) ≤ ((21357615 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2653
  constructor
  · exact (show ((10678805 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((13814242476329 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2653 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((27628484952661 / 18446744073709551616 : ℚ) : ℝ) ≤ ((21357615 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2654 : ((13600072497875 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((1327 / 32 : ℚ) : ℝ) ∧
    heightZ ((1327 / 32 : ℚ) : ℝ) ≤ ((27200144995753 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((13600072497875 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((1327 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1117 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1327 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1117 / 96 : ℚ) : ℝ) ≤ ((27200144995753 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2654 : ((10350253 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((1327 / 32 : ℚ) : ℝ) ∧
    logKernel ((1327 / 32 : ℚ) : ℝ) ≤ ((20700511 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2654
  constructor
  · exact (show ((10350253 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((13600072497875 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1327 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((27200144995753 / 18446744073709551616 : ℚ) : ℝ) ≤ ((20700511 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2655 : ((13389222917173 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2655 / 64 : ℚ) : ℝ) ∧
    heightZ ((2655 / 64 : ℚ) : ℝ) ≤ ((26778445834349 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((13389222917173 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2655 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2237 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2655 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2237 / 192 : ℚ) : ℝ) ≤ ((26778445834349 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2655 : ((10031809 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2655 / 64 : ℚ) : ℝ) ∧
    logKernel ((2655 / 64 : ℚ) : ℝ) ≤ ((20063623 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2655
  constructor
  · exact (show ((10031809 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((13389222917173 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2655 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((26778445834349 / 18446744073709551616 : ℚ) : ℝ) ≤ ((20063623 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2656 : ((3295410564057 / 2305843009213693952 : ℚ) : ℝ) ≤ heightZ ((83 / 2 : ℚ) : ℝ) ∧
    heightZ ((83 / 2 : ℚ) : ℝ) ≤ ((26363284512459 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((3295410564057 / 2305843009213693952 : ℚ) : ℝ) ≤ Real.exp (-((83 / 2 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-35 / 3 : ℚ) : ℝ) ∧
      Real.exp (-((83 / 2 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-35 / 3 : ℚ) : ℝ) ≤ ((26363284512459 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2656 : ((19446325 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((83 / 2 : ℚ) : ℝ) ∧
    logKernel ((83 / 2 : ℚ) : ℝ) ≤ ((9723165 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2656
  constructor
  · exact (show ((19446325 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((3295410564057 / 2305843009213693952 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((83 / 2 : ℚ) : ℝ)) hh).trans
      (show zKernel ((26363284512459 / 18446744073709551616 : ℚ) : ℝ) ≤ ((9723165 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2657 : ((25954559670273 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2657 / 64 : ℚ) : ℝ) ∧
    heightZ ((2657 / 64 : ℚ) : ℝ) ≤ ((6488639917569 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((25954559670273 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2657 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2243 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2657 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2243 / 192 : ℚ) : ℝ) ≤ ((6488639917569 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2657 : ((18848025 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2657 / 64 : ℚ) : ℝ) ∧
    logKernel ((2657 / 64 : ℚ) : ℝ) ≤ ((9424015 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2657
  constructor
  · exact (show ((18848025 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((25954559670273 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2657 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((6488639917569 / 4611686018427387904 : ℚ) : ℝ) ≤ ((9424015 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2658 : ((6388042879857 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((1329 / 32 : ℚ) : ℝ) ∧
    heightZ ((1329 / 32 : ℚ) : ℝ) ≤ ((25552171519431 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((6388042879857 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((1329 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1123 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1329 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1123 / 96 : ℚ) : ℝ) ≤ ((25552171519431 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2658 : ((4567033 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((1329 / 32 : ℚ) : ℝ) ∧
    logKernel ((1329 / 32 : ℚ) : ℝ) ≤ ((18268137 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2658
  constructor
  · exact (show ((4567033 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((6388042879857 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1329 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((25552171519431 / 18446744073709551616 : ℚ) : ℝ) ≤ ((18268137 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2659 : ((6289005454657 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((2659 / 64 : ℚ) : ℝ) ∧
    heightZ ((2659 / 64 : ℚ) : ℝ) ≤ ((25156021818631 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((6289005454657 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((2659 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2249 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2659 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2249 / 192 : ℚ) : ℝ) ≤ ((25156021818631 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2659 : ((553315 / 2251799813685248 : ℚ) : ℝ) ≤ logKernel ((2659 / 64 : ℚ) : ℝ) ∧
    logKernel ((2659 / 64 : ℚ) : ℝ) ≤ ((17706085 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2659
  constructor
  · exact (show ((553315 / 2251799813685248 : ℚ) : ℝ) ≤ zKernel ((6289005454657 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2659 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((25156021818631 / 18446744073709551616 : ℚ) : ℝ) ≤ ((17706085 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2660 : ((24766013849669 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((665 / 16 : ℚ) : ℝ) ∧
    heightZ ((665 / 16 : ℚ) : ℝ) ≤ ((3095751731209 / 2305843009213693952 : ℚ) : ℝ) := by
  have h : ((24766013849669 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((665 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-563 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((665 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-563 / 48 : ℚ) : ℝ) ≤ ((3095751731209 / 2305843009213693952 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2660 : ((17161321 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((665 / 16 : ℚ) : ℝ) ∧
    logKernel ((665 / 16 : ℚ) : ℝ) ≤ ((8580663 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2660
  constructor
  · exact (show ((17161321 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((24766013849669 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((665 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((3095751731209 / 2305843009213693952 : ℚ) : ℝ) ≤ ((8580663 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2661 : ((12191026196913 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2661 / 64 : ℚ) : ℝ) ∧
    heightZ ((2661 / 64 : ℚ) : ℝ) ≤ ((24382052393829 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((12191026196913 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2661 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2255 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2661 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2255 / 192 : ℚ) : ℝ) ≤ ((24382052393829 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2661 : ((16633323 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2661 / 64 : ℚ) : ℝ) ∧
    logKernel ((2661 / 64 : ℚ) : ℝ) ≤ ((1039583 / 4503599627370496 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2661
  constructor
  · exact (show ((16633323 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((12191026196913 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2661 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((24382052393829 / 18446744073709551616 : ℚ) : ℝ) ≤ ((1039583 / 4503599627370496 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2662 : ((24004043708601 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1331 / 32 : ℚ) : ℝ) ∧
    heightZ ((1331 / 32 : ℚ) : ℝ) ≤ ((6001010927151 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((24004043708601 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1331 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1129 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1331 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1129 / 96 : ℚ) : ℝ) ≤ ((6001010927151 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2662 : ((16121569 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1331 / 32 : ℚ) : ℝ) ∧
    logKernel ((1331 / 32 : ℚ) : ℝ) ≤ ((8060787 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2662
  constructor
  · exact (show ((16121569 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((24004043708601 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1331 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((6001010927151 / 4611686018427387904 : ℚ) : ℝ) ≤ ((8060787 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2663 : ((2953986938105 / 2305843009213693952 : ℚ) : ℝ) ≤ heightZ ((2663 / 64 : ℚ) : ℝ) ∧
    heightZ ((2663 / 64 : ℚ) : ℝ) ≤ ((23631895504843 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((2953986938105 / 2305843009213693952 : ℚ) : ℝ) ≤ Real.exp (-((2663 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2261 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2663 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2261 / 192 : ℚ) : ℝ) ≤ ((23631895504843 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2663 : ((15625561 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2663 / 64 : ℚ) : ℝ) ∧
    logKernel ((2663 / 64 : ℚ) : ℝ) ≤ ((7812783 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2663
  constructor
  · exact (show ((15625561 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((2953986938105 / 2305843009213693952 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2663 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((23631895504843 / 18446744073709551616 : ℚ) : ℝ) ≤ ((7812783 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2664 : ((23265516924199 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((333 / 8 : ℚ) : ℝ) ∧
    heightZ ((333 / 8 : ℚ) : ℝ) ≤ ((11632758462101 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((23265516924199 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((333 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-283 / 24 : ℚ) : ℝ) ∧
      Real.exp (-((333 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-283 / 24 : ℚ) : ℝ) ≤ ((11632758462101 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2664 : ((15144813 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((333 / 8 : ℚ) : ℝ) ∧
    logKernel ((333 / 8 : ℚ) : ℝ) ≤ ((7572409 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2664
  constructor
  · exact (show ((15144813 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((23265516924199 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((333 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((11632758462101 / 9223372036854775808 : ℚ) : ℝ) ≤ ((7572409 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2665 : ((22904818516963 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2665 / 64 : ℚ) : ℝ) ∧
    heightZ ((2665 / 64 : ℚ) : ℝ) ≤ ((11452409258483 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((22904818516963 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2665 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2267 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2665 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2267 / 192 : ℚ) : ℝ) ≤ ((11452409258483 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2665 : ((1834857 / 9007199254740992 : ℚ) : ℝ) ≤ logKernel ((2665 / 64 : ℚ) : ℝ) ∧
    logKernel ((2665 / 64 : ℚ) : ℝ) ≤ ((14678861 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2665
  constructor
  · exact (show ((1834857 / 9007199254740992 : ℚ) : ℝ) ≤ zKernel ((22904818516963 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2665 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((11452409258483 / 9223372036854775808 : ℚ) : ℝ) ≤ ((14678861 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2666 : ((22549712220205 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1333 / 32 : ℚ) : ℝ) ∧
    heightZ ((1333 / 32 : ℚ) : ℝ) ≤ ((1409357013763 / 1152921504606846976 : ℚ) : ℝ) := by
  have h : ((22549712220205 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1333 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1135 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1333 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1135 / 96 : ℚ) : ℝ) ≤ ((1409357013763 / 1152921504606846976 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2666 : ((14227235 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1333 / 32 : ℚ) : ℝ) ∧
    logKernel ((1333 / 32 : ℚ) : ℝ) ≤ ((1778405 / 9007199254740992 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2666
  constructor
  · exact (show ((14227235 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((22549712220205 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1333 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1409357013763 / 1152921504606846976 : ℚ) : ℝ) ≤ ((1778405 / 9007199254740992 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2667 : ((22200111336289 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2667 / 64 : ℚ) : ℝ) ∧
    heightZ ((2667 / 64 : ℚ) : ℝ) ≤ ((5550027834073 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((22200111336289 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2667 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2273 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2667 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2273 / 192 : ℚ) : ℝ) ≤ ((5550027834073 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2667 : ((13789509 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2667 / 64 : ℚ) : ℝ) ∧
    logKernel ((2667 / 64 : ℚ) : ℝ) ≤ ((6894757 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2667
  constructor
  · exact (show ((13789509 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((22200111336289 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2667 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((5550027834073 / 4611686018427387904 : ℚ) : ℝ) ≤ ((6894757 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2668 : ((5463982627925 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((667 / 16 : ℚ) : ℝ) ∧
    heightZ ((667 / 16 : ℚ) : ℝ) ≤ ((21855930511703 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((5463982627925 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((667 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-569 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((667 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-569 / 48 : ℚ) : ℝ) ≤ ((21855930511703 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2668 : ((6682625 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((667 / 16 : ℚ) : ℝ) ∧
    logKernel ((667 / 16 : ℚ) : ℝ) ≤ ((13365255 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2668
  constructor
  · exact (show ((6682625 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((5463982627925 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((667 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((21855930511703 / 18446744073709551616 : ℚ) : ℝ) ≤ ((13365255 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2669 : ((21517085716207 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2669 / 64 : ℚ) : ℝ) ∧
    heightZ ((2669 / 64 : ℚ) : ℝ) ≤ ((10758542858105 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((21517085716207 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2669 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2279 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2669 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2279 / 192 : ℚ) : ℝ) ≤ ((10758542858105 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2669 : ((3238511 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((2669 / 64 : ℚ) : ℝ) ∧
    logKernel ((2669 / 64 : ℚ) : ℝ) ≤ ((12954049 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2669
  constructor
  · exact (show ((3238511 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((21517085716207 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2669 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((10758542858105 / 9223372036854775808 : ℚ) : ℝ) ≤ ((12954049 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2670 : ((21183494222345 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1335 / 32 : ℚ) : ℝ) ∧
    heightZ ((1335 / 32 : ℚ) : ℝ) ≤ ((5295873555587 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((21183494222345 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1335 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1141 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1335 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1141 / 96 : ℚ) : ℝ) ≤ ((5295873555587 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2670 : ((6277745 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((1335 / 32 : ℚ) : ℝ) ∧
    logKernel ((1335 / 32 : ℚ) : ℝ) ≤ ((12555495 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2670
  constructor
  · exact (show ((6277745 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((21183494222345 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1335 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((5295873555587 / 4611686018427387904 : ℚ) : ℝ) ≤ ((12555495 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2671 : ((2606884323153 / 2305843009213693952 : ℚ) : ℝ) ≤ heightZ ((2671 / 64 : ℚ) : ℝ) ∧
    heightZ ((2671 / 64 : ℚ) : ℝ) ≤ ((20855074585227 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((2606884323153 / 2305843009213693952 : ℚ) : ℝ) ≤ Real.exp (-((2671 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2285 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2671 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2285 / 192 : ℚ) : ℝ) ≤ ((20855074585227 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2671 : ((6084599 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2671 / 64 : ℚ) : ℝ) ∧
    logKernel ((2671 / 64 : ℚ) : ℝ) ≤ ((12169203 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2671
  constructor
  · exact (show ((6084599 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((2606884323153 / 2305843009213693952 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2671 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((20855074585227 / 18446744073709551616 : ℚ) : ℝ) ≤ ((12169203 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2672 : ((20531746622635 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((167 / 4 : ℚ) : ℝ) ∧
    heightZ ((167 / 4 : ℚ) : ℝ) ≤ ((10265873311319 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((20531746622635 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((167 / 4 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-143 / 12 : ℚ) : ℝ) ∧
      Real.exp (-((167 / 4 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-143 / 12 : ℚ) : ℝ) ≤ ((10265873311319 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2672 : ((11794791 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((167 / 4 : ℚ) : ℝ) ∧
    logKernel ((167 / 4 : ℚ) : ℝ) ≤ ((2948699 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2672
  constructor
  · exact (show ((11794791 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((20531746622635 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((167 / 4 : ℚ) : ℝ)) hh).trans
      (show zKernel ((10265873311319 / 9223372036854775808 : ℚ) : ℝ) ≤ ((2948699 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

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

theorem log_height_bounds_800 : ((268083678266623333 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1321 / 32 : ℚ) : ℝ) ∧
    Real.log ((1321 / 32 : ℚ) : ℝ) ≤ ((33510459783327917 / 9007199254740992 : ℚ) : ℝ) := by
  have hl : Real.exp ((268083678266623333 / 72057594037927936 : ℚ) : ℝ) ≤ ((1321 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1321 / 32 : ℚ) : ℝ) ≤ Real.exp ((33510459783327917 / 9007199254740992 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_800 : heightPower (800 : Fin 988) ≤ ((3620059077224839 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_800
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_800 : heightFactor (800 : Fin 988) ≤ ((926076157 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_800
  obtain ⟨hpl, hph⟩ := kernel_bounds_2641
  obtain ⟨hcl, hch⟩ := kernel_bounds_2642
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2642
  have h : (((1745041 / 512 : ℚ) : ℝ) * (logKernel ((2641 / 64 : ℚ) : ℝ) - logKernel ((1321 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1321 / 32 : ℚ) : ℝ) + Real.log ((1321 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((926076157 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_801 : ((268110946987492915 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2643 / 64 : ℚ) : ℝ) ∧
    Real.log ((2643 / 64 : ℚ) : ℝ) ≤ ((134055473493746459 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((268110946987492915 / 72057594037927936 : ℚ) : ℝ) ≤ ((2643 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2643 / 64 : ℚ) : ℝ) ≤ Real.exp ((134055473493746459 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_801 : heightPower (801 : Fin 988) ≤ ((453070455272105 / 35184372088832 : ℚ) : ℝ) := by
  have hh := log_height_bounds_801
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_801 : heightFactor (801 : Fin 988) ≤ ((225767397 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_801
  obtain ⟨hpl, hph⟩ := kernel_bounds_2642
  obtain ⟨hcl, hch⟩ := kernel_bounds_2643
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2643
  have h : (((6985449 / 2048 : ℚ) : ℝ) * (logKernel ((1321 / 32 : ℚ) : ℝ) - logKernel ((2643 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2643 / 64 : ℚ) : ℝ) + Real.log ((2643 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((225767397 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_802 : ((134069102696488507 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((661 / 16 : ℚ) : ℝ) ∧
    Real.log ((661 / 16 : ℚ) : ℝ) ≤ ((268138205392977017 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((134069102696488507 / 36028797018963968 : ℚ) : ℝ) ≤ ((661 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((661 / 16 : ℚ) : ℝ) ≤ Real.exp ((268138205392977017 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_802 : heightPower (802 : Fin 988) ≤ ((1814534083417183 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_802
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_802 : heightFactor (802 : Fin 988) ≤ ((440317159 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_802
  obtain ⟨hpl, hph⟩ := kernel_bounds_2643
  obtain ⟨hcl, hch⟩ := kernel_bounds_2644
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2644
  have h : (((436921 / 128 : ℚ) : ℝ) * (logKernel ((2643 / 64 : ℚ) : ℝ) - logKernel ((661 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((661 / 16 : ℚ) : ℝ) + Real.log ((661 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((440317159 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_803 : ((268165453490877021 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2645 / 64 : ℚ) : ℝ) ∧
    Real.log ((2645 / 64 : ℚ) : ℝ) ≤ ((8380170421589907 / 2251799813685248 : ℚ) : ℝ) := by
  have hl : Real.exp ((268165453490877021 / 72057594037927936 : ℚ) : ℝ) ≤ ((2645 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2645 / 64 : ℚ) : ℝ) ≤ Real.exp ((8380170421589907 / 2251799813685248 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_803 : heightPower (803 : Fin 988) ≤ ((908393162806973 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_803
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_803 : heightFactor (803 : Fin 988) ≤ ((858756169 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_803
  obtain ⟨hpl, hph⟩ := kernel_bounds_2644
  obtain ⟨hcl, hch⟩ := kernel_bounds_2645
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2645
  have h : (((6996025 / 2048 : ℚ) : ℝ) * (logKernel ((661 / 16 : ℚ) : ℝ) - logKernel ((2645 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2645 / 64 : ℚ) : ℝ) + Real.log ((2645 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((858756169 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_804 : ((268192691288985477 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1323 / 32 : ℚ) : ℝ) ∧
    Real.log ((1323 / 32 : ℚ) : ℝ) ≤ ((33524086411123185 / 9007199254740992 : ℚ) : ℝ) := by
  have hl : Real.exp ((268192691288985477 / 72057594037927936 : ℚ) : ℝ) ≤ ((1323 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1323 / 32 : ℚ) : ℝ) ≤ Real.exp ((33524086411123185 / 9007199254740992 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_804 : heightPower (804 : Fin 988) ≤ ((3638077095387857 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_804
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_804 : heightFactor (804 : Fin 988) ≤ ((418710657 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_804
  obtain ⟨hpl, hph⟩ := kernel_bounds_2645
  obtain ⟨hcl, hch⟩ := kernel_bounds_2646
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2646
  have h : (((1750329 / 512 : ℚ) : ℝ) * (logKernel ((2645 / 64 : ℚ) : ℝ) - logKernel ((1323 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1323 / 32 : ℚ) : ℝ) + Real.log ((1323 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((418710657 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_805 : ((134109959397543045 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2647 / 64 : ℚ) : ℝ) ∧
    Real.log ((2647 / 64 : ℚ) : ℝ) ≤ ((268219918795086093 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((134109959397543045 / 36028797018963968 : ℚ) : ℝ) ≤ ((2647 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2647 / 64 : ℚ) : ℝ) ≤ Real.exp ((268219918795086093 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_805 : heightPower (805 : Fin 988) ≤ ((3642581499344667 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_805
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_805 : heightFactor (805 : Fin 988) ≤ ((816616269 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_805
  obtain ⟨hpl, hph⟩ := kernel_bounds_2646
  obtain ⟨hcl, hch⟩ := kernel_bounds_2647
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2647
  have h : (((7006609 / 2048 : ℚ) : ℝ) * (logKernel ((1323 / 32 : ℚ) : ℝ) - logKernel ((2647 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2647 / 64 : ℚ) : ℝ) + Real.log ((2647 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((816616269 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_806 : ((268247136016953747 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((331 / 8 : ℚ) : ℝ) ∧
    Real.log ((331 / 8 : ℚ) : ℝ) ≤ ((134123568008476875 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((268247136016953747 / 72057594037927936 : ℚ) : ℝ) ≤ ((331 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((331 / 8 : ℚ) : ℝ) ≤ Real.exp ((134123568008476875 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_806 : heightPower (806 : Fin 988) ≤ ((3647085863128691 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_806
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_806 : heightFactor (806 : Fin 988) ≤ ((796327883 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_806
  obtain ⟨hpl, hph⟩ := kernel_bounds_2647
  obtain ⟨hcl, hch⟩ := kernel_bounds_2648
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2648
  have h : (((109561 / 32 : ℚ) : ℝ) * (logKernel ((2647 / 64 : ℚ) : ℝ) - logKernel ((331 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((331 / 8 : ℚ) : ℝ) + Real.log ((331 / 8 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((796327883 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_807 : ((268274342962354531 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2649 / 64 : ℚ) : ℝ) ∧
    Real.log ((2649 / 64 : ℚ) : ℝ) ≤ ((134137171481177267 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((268274342962354531 / 72057594037927936 : ℚ) : ℝ) ≤ ((2649 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2649 / 64 : ℚ) : ℝ) ≤ Real.exp ((134137171481177267 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_807 : heightPower (807 : Fin 988) ≤ ((3651590186770267 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_807
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_807 : heightFactor (807 : Fin 988) ≤ ((776543333 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_807
  obtain ⟨hpl, hph⟩ := kernel_bounds_2648
  obtain ⟨hcl, hch⟩ := kernel_bounds_2649
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2649
  have h : (((7017201 / 2048 : ℚ) : ℝ) * (logKernel ((331 / 8 : ℚ) : ℝ) - logKernel ((2649 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2649 / 64 : ℚ) : ℝ) + Real.log ((2649 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((776543333 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_808 : ((134150769819522865 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((1325 / 32 : ℚ) : ℝ) ∧
    Real.log ((1325 / 32 : ℚ) : ℝ) ≤ ((268301539639045733 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((134150769819522865 / 36028797018963968 : ℚ) : ℝ) ≤ ((1325 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1325 / 32 : ℚ) : ℝ) ≤ Real.exp ((268301539639045733 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_808 : heightPower (808 : Fin 988) ≤ ((228505904393731 / 17592186044416 : ℚ) : ℝ) := by
  have hh := log_height_bounds_808
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_808 : heightFactor (808 : Fin 988) ≤ ((757250113 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_808
  obtain ⟨hpl, hph⟩ := kernel_bounds_2649
  obtain ⟨hcl, hch⟩ := kernel_bounds_2650
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2650
  have h : (((1755625 / 512 : ℚ) : ℝ) * (logKernel ((2649 / 64 : ℚ) : ℝ) - logKernel ((1325 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1325 / 32 : ℚ) : ℝ) + Real.log ((1325 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((757250113 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_809 : ((268328726054775851 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2651 / 64 : ℚ) : ℝ) ∧
    Real.log ((2651 / 64 : ℚ) : ℝ) ≤ ((134164363027387927 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((268328726054775851 / 72057594037927936 : ℚ) : ℝ) ≤ ((2651 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2651 / 64 : ℚ) : ℝ) ≤ Real.exp ((134164363027387927 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_809 : heightPower (809 : Fin 988) ≤ ((1830299356873623 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_809
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_809 : heightFactor (809 : Fin 988) ≤ ((738436029 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_809
  obtain ⟨hpl, hph⟩ := kernel_bounds_2650
  obtain ⟨hcl, hch⟩ := kernel_bounds_2651
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2651
  have h : (((7027801 / 2048 : ℚ) : ℝ) * (logKernel ((1325 / 32 : ℚ) : ℝ) - logKernel ((2651 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2651 / 64 : ℚ) : ℝ) + Real.log ((2651 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((738436029 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_810 : ((268355902217284635 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((663 / 16 : ℚ) : ℝ) ∧
    Real.log ((663 / 16 : ℚ) : ℝ) ≤ ((134177951108642319 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((268355902217284635 / 72057594037927936 : ℚ) : ℝ) ≤ ((663 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((663 / 16 : ℚ) : ℝ) ≤ Real.exp ((134177951108642319 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_810 : heightPower (810 : Fin 988) ≤ ((1832551458571575 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_810
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_810 : heightFactor (810 : Fin 988) ≤ ((720089187 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_810
  obtain ⟨hpl, hph⟩ := kernel_bounds_2651
  obtain ⟨hcl, hch⟩ := kernel_bounds_2652
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2652
  have h : (((439569 / 128 : ℚ) : ℝ) * (logKernel ((2651 / 64 : ℚ) : ℝ) - logKernel ((663 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((663 / 16 : ℚ) : ℝ) + Real.log ((663 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((720089187 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_811 : ((268383068134303069 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2653 / 64 : ℚ) : ℝ) ∧
    Real.log ((2653 / 64 : ℚ) : ℝ) ≤ ((8386970879196971 / 2251799813685248 : ℚ) : ℝ) := by
  have hl : Real.exp ((268383068134303069 / 72057594037927936 : ℚ) : ℝ) ≤ ((2653 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2653 / 64 : ℚ) : ℝ) ≤ Real.exp ((8386970879196971 / 2251799813685248 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_811 : heightPower (811 : Fin 988) ≤ ((3669607080517607 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_811
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_811 : heightFactor (811 : Fin 988) ≤ ((702197989 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_811
  obtain ⟨hpl, hph⟩ := kernel_bounds_2652
  obtain ⟨hcl, hch⟩ := kernel_bounds_2653
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2653
  have h : (((7038409 / 2048 : ℚ) : ℝ) * (logKernel ((663 / 16 : ℚ) : ℝ) - logKernel ((2653 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2653 / 64 : ℚ) : ℝ) + Real.log ((2653 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((702197989 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_812 : ((33551277976694175 / 9007199254740992 : ℚ) : ℝ) ≤ Real.log ((1327 / 32 : ℚ) : ℝ) ∧
    Real.log ((1327 / 32 : ℚ) : ℝ) ≤ ((268410223813553403 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((33551277976694175 / 9007199254740992 : ℚ) : ℝ) ≤ ((1327 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1327 / 32 : ℚ) : ℝ) ≤ Real.exp ((268410223813553403 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_812 : heightPower (812 : Fin 988) ≤ ((1837055601950391 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_812
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_812 : heightFactor (812 : Fin 988) ≤ ((684751127 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_812
  obtain ⟨hpl, hph⟩ := kernel_bounds_2653
  obtain ⟨hcl, hch⟩ := kernel_bounds_2654
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2654
  have h : (((1760929 / 512 : ℚ) : ℝ) * (logKernel ((2653 / 64 : ℚ) : ℝ) - logKernel ((1327 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1327 / 32 : ℚ) : ℝ) + Real.log ((1327 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((684751127 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_813 : ((67109342315687287 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((2655 / 64 : ℚ) : ℝ) ∧
    Real.log ((2655 / 64 : ℚ) : ℝ) ≤ ((268437369262749151 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((67109342315687287 / 18014398509481984 : ℚ) : ℝ) ≤ ((2655 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2655 / 64 : ℚ) : ℝ) ≤ Real.exp ((268437369262749151 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_813 : heightPower (813 : Fin 988) ≤ ((3678615287322807 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_813
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_813 : heightFactor (813 : Fin 988) ≤ ((667737569 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_813
  obtain ⟨hpl, hph⟩ := kernel_bounds_2654
  obtain ⟨hcl, hch⟩ := kernel_bounds_2655
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2655
  have h : (((7049025 / 2048 : ℚ) : ℝ) * (logKernel ((1327 / 32 : ℚ) : ℝ) - logKernel ((2655 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2655 / 64 : ℚ) : ℝ) + Real.log ((2655 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((667737569 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_814 : ((67116126122398779 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((83 / 2 : ℚ) : ℝ) ∧
    Real.log ((83 / 2 : ℚ) : ℝ) ≤ ((268464504489595119 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((67116126122398779 / 18014398509481984 : ℚ) : ℝ) ≤ ((83 / 2 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((83 / 2 : ℚ) : ℝ) ≤ Real.exp ((268464504489595119 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_814 : heightPower (814 : Fin 988) ≤ ((1841559665406889 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_814
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_814 : heightFactor (814 : Fin 988) ≤ ((325573281 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_814
  obtain ⟨hpl, hph⟩ := kernel_bounds_2655
  obtain ⟨hcl, hch⟩ := kernel_bounds_2656
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2656
  have h : (((6889 / 2 : ℚ) : ℝ) * (logKernel ((2655 / 64 : ℚ) : ℝ) - logKernel ((83 / 2 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((83 / 2 : ℚ) : ℝ) + Real.log ((83 / 2 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((325573281 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_815 : ((134245814750893705 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2657 / 64 : ℚ) : ℝ) ∧
    Real.log ((2657 / 64 : ℚ) : ℝ) ≤ ((268491629501787413 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((134245814750893705 / 36028797018963968 : ℚ) : ℝ) ≤ ((2657 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2657 / 64 : ℚ) : ℝ) ≤ Real.exp ((268491629501787413 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_815 : heightPower (815 : Fin 988) ≤ ((3687623334403759 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_815
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_815 : heightFactor (815 : Fin 988) ≤ ((634967615 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_815
  obtain ⟨hpl, hph⟩ := kernel_bounds_2656
  obtain ⟨hcl, hch⟩ := kernel_bounds_2657
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2657
  have h : (((7059649 / 2048 : ℚ) : ℝ) * (logKernel ((83 / 2 : ℚ) : ℝ) - logKernel ((2657 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2657 / 64 : ℚ) : ℝ) + Real.log ((2657 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((634967615 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_816 : ((268518744307013445 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1329 / 32 : ℚ) : ℝ) ∧
    Real.log ((1329 / 32 : ℚ) : ℝ) ≤ ((33564843038376681 / 9007199254740992 : ℚ) : ℝ) := by
  have hl : Real.exp ((268518744307013445 / 72057594037927936 : ℚ) : ℝ) ≤ ((1329 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1329 / 32 : ℚ) : ℝ) ≤ Real.exp ((33564843038376681 / 9007199254740992 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_816 : heightPower (816 : Fin 988) ≤ ((3692127298122777 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_816
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_816 : heightFactor (816 : Fin 988) ≤ ((619190499 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_816
  obtain ⟨hpl, hph⟩ := kernel_bounds_2657
  obtain ⟨hcl, hch⟩ := kernel_bounds_2658
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2658
  have h : (((1766241 / 512 : ℚ) : ℝ) * (logKernel ((2657 / 64 : ℚ) : ℝ) - logKernel ((1329 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1329 / 32 : ℚ) : ℝ) + Real.log ((1329 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((619190499 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_817 : ((268545848912951963 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2659 / 64 : ℚ) : ℝ) ∧
    Real.log ((2659 / 64 : ℚ) : ℝ) ≤ ((134272924456475983 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((268545848912951963 / 72057594037927936 : ℚ) : ℝ) ≤ ((2659 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2659 / 64 : ℚ) : ℝ) ≤ Real.exp ((134272924456475983 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_817 : heightPower (817 : Fin 988) ≤ ((924157805500207 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_817
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_817 : heightFactor (817 : Fin 988) ≤ ((603805241 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_817
  obtain ⟨hpl, hph⟩ := kernel_bounds_2658
  obtain ⟨hcl, hch⟩ := kernel_bounds_2659
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2659
  have h : (((7070281 / 2048 : ℚ) : ℝ) * (logKernel ((1329 / 32 : ℚ) : ℝ) - logKernel ((2659 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2659 / 64 : ℚ) : ℝ) + Real.log ((2659 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((603805241 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_818 : ((134286471663636521 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((665 / 16 : ℚ) : ℝ) ∧
    Real.log ((665 / 16 : ℚ) : ℝ) ≤ ((268572943327273045 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((134286471663636521 / 36028797018963968 : ℚ) : ℝ) ≤ ((665 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((665 / 16 : ℚ) : ℝ) ≤ Real.exp ((268572943327273045 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_818 : heightPower (818 : Fin 988) ≤ ((1850567553033937 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_818
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_818 : heightFactor (818 : Fin 988) ≤ ((9200033 / 4398046511104 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_818
  obtain ⟨hpl, hph⟩ := kernel_bounds_2659
  obtain ⟨hcl, hch⟩ := kernel_bounds_2660
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2660
  have h : (((442225 / 128 : ℚ) : ℝ) * (logKernel ((2659 / 64 : ℚ) : ℝ) - logKernel ((665 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((665 / 16 : ℚ) : ℝ) + Real.log ((665 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((9200033 / 4398046511104 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_819 : ((268600027557638113 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2661 / 64 : ℚ) : ℝ) ∧
    Real.log ((2661 / 64 : ℚ) : ℝ) ≤ ((67150006889409529 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((268600027557638113 / 72057594037927936 : ℚ) : ℝ) ≤ ((2661 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2661 / 64 : ℚ) : ℝ) ≤ Real.exp ((67150006889409529 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_819 : heightPower (819 : Fin 988) ≤ ((3705638950353841 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_819
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_819 : heightFactor (819 : Fin 988) ≤ ((287085813 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_819
  obtain ⟨hpl, hph⟩ := kernel_bounds_2660
  obtain ⟨hcl, hch⟩ := kernel_bounds_2661
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2661
  have h : (((7080921 / 2048 : ℚ) : ℝ) * (logKernel ((665 / 16 : ℚ) : ℝ) - logKernel ((2661 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2661 / 64 : ℚ) : ℝ) + Real.log ((2661 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((287085813 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_820 : ((268627101611699971 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1331 / 32 : ℚ) : ℝ) ∧
    Real.log ((1331 / 32 : ℚ) : ℝ) ≤ ((134313550805849987 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((268627101611699971 / 72057594037927936 : ℚ) : ℝ) ≤ ((1331 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1331 / 32 : ℚ) : ℝ) ≤ Real.exp ((134313550805849987 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_820 : heightPower (820 : Fin 988) ≤ ((3710142754888625 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_820
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_820 : heightFactor (820 : Fin 988) ≤ ((559904533 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_820
  obtain ⟨hpl, hph⟩ := kernel_bounds_2661
  obtain ⟨hcl, hch⟩ := kernel_bounds_2662
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2662
  have h : (((1771561 / 512 : ℚ) : ℝ) * (logKernel ((2661 / 64 : ℚ) : ℝ) - logKernel ((1331 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1331 / 32 : ℚ) : ℝ) + Real.log ((1331 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((559904533 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_821 : ((268654165497102787 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2663 / 64 : ℚ) : ℝ) ∧
    Real.log ((2663 / 64 : ℚ) : ℝ) ≤ ((134327082748551395 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((268654165497102787 / 72057594037927936 : ℚ) : ℝ) ≤ ((2663 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2663 / 64 : ℚ) : ℝ) ≤ Real.exp ((134327082748551395 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_821 : heightPower (821 : Fin 988) ≤ ((3714646519702083 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_821
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_821 : heightFactor (821 : Fin 988) ≤ ((136497953 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_821
  obtain ⟨hpl, hph⟩ := kernel_bounds_2662
  obtain ⟨hcl, hch⟩ := kernel_bounds_2663
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2663
  have h : (((7091569 / 2048 : ℚ) : ℝ) * (logKernel ((1331 / 32 : ℚ) : ℝ) - logKernel ((2663 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2663 / 64 : ℚ) : ℝ) + Real.log ((2663 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((136497953 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_822 : ((268681219221482123 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((333 / 8 : ℚ) : ℝ) ∧
    Real.log ((333 / 8 : ℚ) : ℝ) ≤ ((134340609610741063 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((268681219221482123 / 72057594037927936 : ℚ) : ℝ) ≤ ((333 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((333 / 8 : ℚ) : ℝ) ≤ Real.exp ((134340609610741063 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_822 : heightPower (822 : Fin 988) ≤ ((929787561206011 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_822
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_822 : heightFactor (822 : Fin 988) ≤ ((66553083 / 35184372088832 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_822
  obtain ⟨hpl, hph⟩ := kernel_bounds_2663
  obtain ⟨hcl, hch⟩ := kernel_bounds_2664
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2664
  have h : (((110889 / 32 : ℚ) : ℝ) * (logKernel ((2663 / 64 : ℚ) : ℝ) - logKernel ((333 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((333 / 8 : ℚ) : ℝ) + Real.log ((333 / 8 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((66553083 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_823 : ((16794266424529059 / 4503599627370496 : ℚ) : ℝ) ≤ Real.log ((2665 / 64 : ℚ) : ℝ) ∧
    Real.log ((2665 / 64 : ℚ) : ℝ) ≤ ((268708262792464947 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((16794266424529059 / 4503599627370496 : ℚ) : ℝ) ≤ ((2665 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2665 / 64 : ℚ) : ℝ) ≤ Real.exp ((268708262792464947 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_823 : heightPower (823 : Fin 988) ≤ ((930913482571075 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_823
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_823 : heightFactor (823 : Fin 988) ≤ ((519194511 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_823
  obtain ⟨hpl, hph⟩ := kernel_bounds_2664
  obtain ⟨hcl, hch⟩ := kernel_bounds_2665
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2665
  have h : (((7102225 / 2048 : ℚ) : ℝ) * (logKernel ((333 / 8 : ℚ) : ℝ) - logKernel ((2665 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2665 / 64 : ℚ) : ℝ) + Real.log ((2665 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((519194511 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_824 : ((268735296217669631 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1333 / 32 : ℚ) : ℝ) ∧
    Real.log ((1333 / 32 : ℚ) : ℝ) ≤ ((134367648108834817 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((268735296217669631 / 72057594037927936 : ℚ) : ℝ) ≤ ((1333 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1333 / 32 : ℚ) : ℝ) ≤ Real.exp ((134367648108834817 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_824 : heightPower (824 : Fin 988) ≤ ((1864078788056305 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_824
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_824 : heightFactor (824 : Fin 988) ≤ ((253146493 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_824
  obtain ⟨hpl, hph⟩ := kernel_bounds_2665
  obtain ⟨hcl, hch⟩ := kernel_bounds_2666
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2666
  have h : (((1776889 / 512 : ℚ) : ℝ) * (logKernel ((2665 / 64 : ℚ) : ℝ) - logKernel ((1333 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1333 / 32 : ℚ) : ℝ) + Real.log ((1333 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((253146493 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_825 : ((268762319504705993 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2667 / 64 : ℚ) : ℝ) ∧
    Real.log ((2667 / 64 : ℚ) : ℝ) ≤ ((67190579876176499 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((268762319504705993 / 72057594037927936 : ℚ) : ℝ) ≤ ((2667 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2667 / 64 : ℚ) : ℝ) ≤ Real.exp ((67190579876176499 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_825 : heightPower (825 : Fin 988) ≤ ((3732661182338699 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_825
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_825 : heightFactor (825 : Fin 988) ≤ ((123427983 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_825
  obtain ⟨hpl, hph⟩ := kernel_bounds_2666
  obtain ⟨hcl, hch⟩ := kernel_bounds_2667
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2667
  have h : (((7112889 / 2048 : ℚ) : ℝ) * (logKernel ((1333 / 32 : ℚ) : ℝ) - logKernel ((2667 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2667 / 64 : ℚ) : ℝ) + Real.log ((2667 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((123427983 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_826 : ((268789332661175281 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((667 / 16 : ℚ) : ℝ) ∧
    Real.log ((667 / 16 : ℚ) : ℝ) ≤ ((67197333165293821 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((268789332661175281 / 72057594037927936 : ℚ) : ℝ) ≤ ((667 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((667 / 16 : ℚ) : ℝ) ≤ Real.exp ((67197333165293821 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_826 : heightPower (826 : Fin 988) ≤ ((3737164748992261 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_826
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_826 : heightFactor (826 : Fin 988) ≤ ((481443391 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_826
  obtain ⟨hpl, hph⟩ := kernel_bounds_2667
  obtain ⟨hcl, hch⟩ := kernel_bounds_2668
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2668
  have h : (((444889 / 128 : ℚ) : ℝ) * (logKernel ((2667 / 64 : ℚ) : ℝ) - logKernel ((667 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((667 / 16 : ℚ) : ℝ) + Real.log ((667 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((481443391 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_827 : ((33602041961833775 / 9007199254740992 : ℚ) : ℝ) ≤ Real.log ((2669 / 64 : ℚ) : ℝ) ∧
    Real.log ((2669 / 64 : ℚ) : ℝ) ≤ ((268816335694670203 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((33602041961833775 / 9007199254740992 : ℚ) : ℝ) ≤ ((2669 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2669 / 64 : ℚ) : ℝ) ≤ Real.exp ((268816335694670203 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_827 : heightPower (827 : Fin 988) ≤ ((3741668276102955 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_827
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_827 : heightFactor (827 : Fin 988) ≤ ((469479605 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_827
  obtain ⟨hpl, hph⟩ := kernel_bounds_2668
  obtain ⟨hcl, hch⟩ := kernel_bounds_2669
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2669
  have h : (((7123561 / 2048 : ℚ) : ℝ) * (logKernel ((667 / 16 : ℚ) : ℝ) - logKernel ((2669 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2669 / 64 : ℚ) : ℝ) + Real.log ((2669 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((469479605 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_828 : ((67210832153193731 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((1335 / 32 : ℚ) : ℝ) ∧
    Real.log ((1335 / 32 : ℚ) : ℝ) ≤ ((268843328612774927 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((67210832153193731 / 18014398509481984 : ℚ) : ℝ) ≤ ((1335 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1335 / 32 : ℚ) : ℝ) ≤ Real.exp ((268843328612774927 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_828 : heightPower (828 : Fin 988) ≤ ((1873085881850203 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_828
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_828 : heightFactor (828 : Fin 988) ≤ ((28613313 / 17592186044416 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_828
  obtain ⟨hpl, hph⟩ := kernel_bounds_2669
  obtain ⟨hcl, hch⟩ := kernel_bounds_2670
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2670
  have h : (((1782225 / 512 : ℚ) : ℝ) * (logKernel ((2669 / 64 : ℚ) : ℝ) - logKernel ((1335 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1335 / 32 : ℚ) : ℝ) + Real.log ((1335 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((28613313 / 17592186044416 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_829 : ((134435155711532553 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2671 / 64 : ℚ) : ℝ) ∧
    Real.log ((2671 / 64 : ℚ) : ℝ) ≤ ((268870311423065109 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((134435155711532553 / 36028797018963968 : ℚ) : ℝ) ≤ ((2671 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2671 / 64 : ℚ) : ℝ) ≤ Real.exp ((268870311423065109 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_829 : heightPower (829 : Fin 988) ≤ ((1875337605907103 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_829
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_829 : heightFactor (829 : Fin 988) ≤ ((111609055 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_829
  obtain ⟨hpl, hph⟩ := kernel_bounds_2670
  obtain ⟨hcl, hch⟩ := kernel_bounds_2671
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2671
  have h : (((7134241 / 2048 : ℚ) : ℝ) * (logKernel ((1335 / 32 : ℚ) : ℝ) - logKernel ((2671 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2671 / 64 : ℚ) : ℝ) + Real.log ((2671 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((111609055 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_830 : ((268897284133107891 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((167 / 4 : ℚ) : ℝ) ∧
    Real.log ((167 / 4 : ℚ) : ℝ) ≤ ((134448642066553947 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((268897284133107891 / 72057594037927936 : ℚ) : ℝ) ≤ ((167 / 4 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((167 / 4 : ℚ) : ℝ) ≤ Real.exp ((134448642066553947 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_830 : heightPower (830 : Fin 988) ≤ ((1877589310236957 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_830
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_830 : heightFactor (830 : Fin 988) ≤ ((435342047 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_830
  obtain ⟨hpl, hph⟩ := kernel_bounds_2671
  obtain ⟨hcl, hch⟩ := kernel_bounds_2672
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2672
  have h : (((27889 / 8 : ℚ) : ℝ) * (logKernel ((2671 / 64 : ℚ) : ℝ) - logKernel ((167 / 4 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((167 / 4 : ℚ) : ℝ) + Real.log ((167 / 4 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((435342047 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_831 : ((268924246750461931 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2673 / 64 : ℚ) : ℝ) ∧
    Real.log ((2673 / 64 : ℚ) : ℝ) ≤ ((134462123375230967 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((268924246750461931 / 72057594037927936 : ℚ) : ℝ) ≤ ((2673 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2673 / 64 : ℚ) : ℝ) ≤ Real.exp ((134462123375230967 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_831 : heightPower (831 : Fin 988) ≤ ((3759681989709057 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_831
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_831 : heightFactor (831 : Fin 988) ≤ ((26532717 / 17592186044416 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_831
  obtain ⟨hpl, hph⟩ := kernel_bounds_2672
  obtain ⟨hcl, hch⟩ := kernel_bounds_2673
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2673
  have h : (((7144929 / 2048 : ℚ) : ℝ) * (logKernel ((167 / 4 : ℚ) : ℝ) - logKernel ((2673 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2673 / 64 : ℚ) : ℝ) + Real.log ((2673 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((26532717 / 17592186044416 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

end LegendreK6.M2Pilot.Enclosures.Height025
