import LegendreK6.M2PilotDefinitions
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp

/-! Generated proposals: every bound is checked by Lean, not by trusting Arb. -/
namespace LegendreK6.M2Pilot.Enclosures.Height024
set_option maxRecDepth 100000
set_option maxHeartbeats 0

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

theorem height_z_bounds_2610 : ((3380871720695 / 1152921504606846976 : ℚ) : ℝ) ≤ heightZ ((1305 / 32 : ℚ) : ℝ) ∧
    heightZ ((1305 / 32 : ℚ) : ℝ) ≤ ((54093947531123 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((3380871720695 / 1152921504606846976 : ℚ) : ℝ) ≤ Real.exp (-((1305 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1051 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1305 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1051 / 96 : ℚ) : ℝ) ≤ ((54093947531123 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2610 : ((81872095 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1305 / 32 : ℚ) : ℝ) ∧
    logKernel ((1305 / 32 : ℚ) : ℝ) ≤ ((20468025 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2610
  constructor
  · exact (show ((81872095 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((3380871720695 / 1152921504606846976 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1305 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((54093947531123 / 18446744073709551616 : ℚ) : ℝ) ≤ ((20468025 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2611 : ((53255298607945 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2611 / 64 : ℚ) : ℝ) ∧
    heightZ ((2611 / 64 : ℚ) : ℝ) ≤ ((13313824651987 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((53255298607945 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2611 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2105 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2611 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2105 / 192 : ℚ) : ℝ) ≤ ((13313824651987 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2611 : ((79353155 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2611 / 64 : ℚ) : ℝ) ∧
    logKernel ((2611 / 64 : ℚ) : ℝ) ≤ ((9919145 / 9007199254740992 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2611
  constructor
  · exact (show ((79353155 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((53255298607945 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2611 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((13313824651987 / 4611686018427387904 : ℚ) : ℝ) ≤ ((9919145 / 9007199254740992 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2612 : ((52429651731181 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((653 / 16 : ℚ) : ℝ) ∧
    heightZ ((653 / 16 : ℚ) : ℝ) ≤ ((3276853233199 / 1152921504606846976 : ℚ) : ℝ) := by
  have h : ((52429651731181 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((653 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-527 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((653 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-527 / 48 : ℚ) : ℝ) ≤ ((3276853233199 / 1152921504606846976 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2612 : ((76911715 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((653 / 16 : ℚ) : ℝ) ∧
    logKernel ((653 / 16 : ℚ) : ℝ) ≤ ((9613965 / 9007199254740992 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2612
  constructor
  · exact (show ((76911715 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((52429651731181 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((653 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((3276853233199 / 1152921504606846976 : ℚ) : ℝ) ≤ ((9613965 / 9007199254740992 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2613 : ((25808402661391 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2613 / 64 : ℚ) : ℝ) ∧
    heightZ ((2613 / 64 : ℚ) : ℝ) ≤ ((51616805322785 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((25808402661391 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2613 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2111 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2613 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2111 / 192 : ℚ) : ℝ) ≤ ((51616805322785 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2613 : ((74545391 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2613 / 64 : ℚ) : ℝ) ∧
    logKernel ((2613 / 64 : ℚ) : ℝ) ≤ ((18636349 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2613
  constructor
  · exact (show ((74545391 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((25808402661391 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2613 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((51616805322785 / 18446744073709551616 : ℚ) : ℝ) ≤ ((18636349 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2614 : ((50816560929881 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1307 / 32 : ℚ) : ℝ) ∧
    heightZ ((1307 / 32 : ℚ) : ℝ) ≤ ((12704140232471 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((50816560929881 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1307 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1057 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1307 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1057 / 96 : ℚ) : ℝ) ≤ ((12704140232471 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2614 : ((36125935 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((1307 / 32 : ℚ) : ℝ) ∧
    logKernel ((1307 / 32 : ℚ) : ℝ) ≤ ((72251875 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2614
  constructor
  · exact (show ((36125935 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((50816560929881 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1307 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((12704140232471 / 4611686018427387904 : ℚ) : ℝ) ≤ ((72251875 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2615 : ((3126795198521 / 1152921504606846976 : ℚ) : ℝ) ≤ heightZ ((2615 / 64 : ℚ) : ℝ) ∧
    heightZ ((2615 / 64 : ℚ) : ℝ) ≤ ((50028723176339 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((3126795198521 / 1152921504606846976 : ℚ) : ℝ) ≤ Real.exp (-((2615 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2117 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2615 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2117 / 192 : ℚ) : ℝ) ≤ ((50028723176339 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2615 : ((35014457 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2615 / 64 : ℚ) : ℝ) ∧
    logKernel ((2615 / 64 : ℚ) : ℝ) ≤ ((70028919 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2615
  constructor
  · exact (show ((35014457 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((3126795198521 / 1152921504606846976 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2615 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((50028723176339 / 18446744073709551616 : ℚ) : ℝ) ≤ ((70028919 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2616 : ((49253099715033 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((327 / 8 : ℚ) : ℝ) ∧
    heightZ ((327 / 8 : ℚ) : ℝ) ≤ ((12313274928759 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((49253099715033 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((327 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-265 / 24 : ℚ) : ℝ) ∧
      Real.exp (-((327 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-265 / 24 : ℚ) : ℝ) ≤ ((12313274928759 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2616 : ((33937175 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((327 / 8 : ℚ) : ℝ) ∧
    logKernel ((327 / 8 : ℚ) : ℝ) ≤ ((67874355 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2616
  constructor
  · exact (show ((33937175 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((49253099715033 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((327 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((12313274928759 / 4611686018427387904 : ℚ) : ℝ) ≤ ((67874355 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2617 : ((24244750590461 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2617 / 64 : ℚ) : ℝ) ∧
    heightZ ((2617 / 64 : ℚ) : ℝ) ≤ ((48489501180925 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((24244750590461 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2617 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2123 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2617 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2123 / 192 : ℚ) : ℝ) ≤ ((48489501180925 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2617 : ((16446519 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((2617 / 64 : ℚ) : ℝ) ∧
    logKernel ((2617 / 64 : ℚ) : ℝ) ≤ ((65786081 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2617
  constructor
  · exact (show ((16446519 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((24244750590461 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2617 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((48489501180925 / 18446744073709551616 : ℚ) : ℝ) ≤ ((65786081 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2618 : ((47737741144787 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1309 / 32 : ℚ) : ℝ) ∧
    heightZ ((1309 / 32 : ℚ) : ℝ) ≤ ((23868870572395 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((47737741144787 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1309 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1063 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1309 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1063 / 96 : ℚ) : ℝ) ≤ ((23868870572395 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2618 : ((63762051 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1309 / 32 : ℚ) : ℝ) ∧
    logKernel ((1309 / 32 : ℚ) : ℝ) ≤ ((7970257 / 9007199254740992 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2618
  constructor
  · exact (show ((63762051 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((47737741144787 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1309 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((23868870572395 / 9223372036854775808 : ℚ) : ℝ) ≤ ((7970257 / 9007199254740992 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2619 : ((46997636067729 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2619 / 64 : ℚ) : ℝ) ∧
    heightZ ((2619 / 64 : ℚ) : ℝ) ≤ ((11749409016933 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((46997636067729 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2619 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2129 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2619 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2129 / 192 : ℚ) : ℝ) ≤ ((11749409016933 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2619 : ((61800299 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2619 / 64 : ℚ) : ℝ) ∧
    logKernel ((2619 / 64 : ℚ) : ℝ) ≤ ((3862519 / 4503599627370496 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2619
  constructor
  · exact (show ((61800299 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((46997636067729 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2619 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((11749409016933 / 4611686018427387904 : ℚ) : ℝ) ≤ ((3862519 / 4503599627370496 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2620 : ((11567251314089 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((655 / 16 : ℚ) : ℝ) ∧
    heightZ ((655 / 16 : ℚ) : ℝ) ≤ ((46269005256359 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((11567251314089 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((655 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-533 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((655 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-533 / 48 : ℚ) : ℝ) ≤ ((46269005256359 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2620 : ((7487363 / 9007199254740992 : ℚ) : ℝ) ≤ logKernel ((655 / 16 : ℚ) : ℝ) ∧
    logKernel ((655 / 16 : ℚ) : ℝ) ≤ ((59898909 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2620
  constructor
  · exact (show ((7487363 / 9007199254740992 : ℚ) : ℝ) ≤ zKernel ((11567251314089 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((655 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((46269005256359 / 18446744073709551616 : ℚ) : ℝ) ≤ ((59898909 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2621 : ((45551670818667 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2621 / 64 : ℚ) : ℝ) ∧
    heightZ ((2621 / 64 : ℚ) : ℝ) ≤ ((22775835409335 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((45551670818667 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2621 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2135 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2621 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2135 / 192 : ℚ) : ℝ) ≤ ((22775835409335 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2621 : ((7257001 / 9007199254740992 : ℚ) : ℝ) ≤ logKernel ((2621 / 64 : ℚ) : ℝ) ∧
    logKernel ((2621 / 64 : ℚ) : ℝ) ≤ ((58056013 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2621
  constructor
  · exact (show ((7257001 / 9007199254740992 : ℚ) : ℝ) ≤ zKernel ((45551670818667 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2621 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((22775835409335 / 9223372036854775808 : ℚ) : ℝ) ≤ ((58056013 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2622 : ((44845457620621 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1311 / 32 : ℚ) : ℝ) ∧
    heightZ ((1311 / 32 : ℚ) : ℝ) ≤ ((2802841101289 / 1152921504606846976 : ℚ) : ℝ) := by
  have h : ((44845457620621 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1311 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1069 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1311 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1069 / 96 : ℚ) : ℝ) ≤ ((2802841101289 / 1152921504606846976 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2622 : ((14067453 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((1311 / 32 : ℚ) : ℝ) ∧
    logKernel ((1311 / 32 : ℚ) : ℝ) ≤ ((56269817 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2622
  constructor
  · exact (show ((14067453 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((44845457620621 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1311 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((2802841101289 / 1152921504606846976 : ℚ) : ℝ) ≤ ((56269817 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2623 : ((44150193243379 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2623 / 64 : ℚ) : ℝ) ∧
    heightZ ((2623 / 64 : ℚ) : ℝ) ≤ ((22075096621691 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((44150193243379 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2623 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2141 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2623 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2141 / 192 : ℚ) : ℝ) ≤ ((22075096621691 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2623 : ((13634643 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((2623 / 64 : ℚ) : ℝ) ∧
    logKernel ((2623 / 64 : ℚ) : ℝ) ≤ ((54538577 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2623
  constructor
  · exact (show ((13634643 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((44150193243379 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2623 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((22075096621691 / 9223372036854775808 : ℚ) : ℝ) ≤ ((54538577 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2624 : ((43465707941207 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((41 / 1 : ℚ) : ℝ) ∧
    heightZ ((41 / 1 : ℚ) : ℝ) ≤ ((21732853970605 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((43465707941207 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((41 / 1 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-67 / 6 : ℚ) : ℝ) ∧
      Real.exp (-((41 / 1 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-67 / 6 : ℚ) : ℝ) ≤ ((21732853970605 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2624 : ((52860597 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((41 / 1 : ℚ) : ℝ) ∧
    logKernel ((41 / 1 : ℚ) : ℝ) ≤ ((26430301 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2624
  constructor
  · exact (show ((52860597 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((43465707941207 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((41 / 1 : ℚ) : ℝ)) hh).trans
      (show zKernel ((21732853970605 / 9223372036854775808 : ℚ) : ℝ) ≤ ((26430301 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2625 : ((42791834600035 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2625 / 64 : ℚ) : ℝ) ∧
    heightZ ((2625 / 64 : ℚ) : ℝ) ≤ ((21395917300019 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((42791834600035 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2625 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2147 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2625 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2147 / 192 : ℚ) : ℝ) ≤ ((21395917300019 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2625 : ((51234247 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2625 / 64 : ℚ) : ℝ) ∧
    logKernel ((2625 / 64 : ℚ) : ℝ) ≤ ((12808563 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2625
  constructor
  · exact (show ((51234247 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((42791834600035 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2625 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((21395917300019 / 9223372036854775808 : ℚ) : ℝ) ≤ ((12808563 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2626 : ((10532102174165 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((1313 / 32 : ℚ) : ℝ) ∧
    heightZ ((1313 / 32 : ℚ) : ℝ) ≤ ((42128408696663 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((10532102174165 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((1313 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1075 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1313 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1075 / 96 : ℚ) : ℝ) ≤ ((42128408696663 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2626 : ((49657935 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1313 / 32 : ℚ) : ℝ) ∧
    logKernel ((1313 / 32 : ℚ) : ℝ) ≤ ((12414485 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2626
  constructor
  · exact (show ((49657935 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((10532102174165 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1313 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((42128408696663 / 18446744073709551616 : ℚ) : ℝ) ≤ ((12414485 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2627 : ((41475268258569 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2627 / 64 : ℚ) : ℝ) ∧
    heightZ ((2627 / 64 : ℚ) : ℝ) ≤ ((10368817064643 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((41475268258569 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2627 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2153 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2627 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2153 / 192 : ℚ) : ℝ) ≤ ((10368817064643 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2627 : ((48130121 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2627 / 64 : ℚ) : ℝ) ∧
    logKernel ((2627 / 64 : ℚ) : ℝ) ≤ ((24065063 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2627
  constructor
  · exact (show ((48130121 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((41475268258569 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2627 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((10368817064643 / 4611686018427387904 : ℚ) : ℝ) ≤ ((24065063 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2628 : ((40832253824405 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((657 / 16 : ℚ) : ℝ) ∧
    heightZ ((657 / 16 : ℚ) : ℝ) ≤ ((5104031728051 / 2305843009213693952 : ℚ) : ℝ) := by
  have h : ((40832253824405 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((657 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-539 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((657 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-539 / 48 : ℚ) : ℝ) ≤ ((5104031728051 / 2305843009213693952 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2628 : ((46649313 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((657 / 16 : ℚ) : ℝ) ∧
    logKernel ((657 / 16 : ℚ) : ℝ) ≤ ((23324659 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2628
  constructor
  · exact (show ((46649313 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((40832253824405 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((657 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((5104031728051 / 2305843009213693952 : ℚ) : ℝ) ≤ ((23324659 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2629 : ((40199208405027 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2629 / 64 : ℚ) : ℝ) ∧
    heightZ ((2629 / 64 : ℚ) : ℝ) ≤ ((20099604202515 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((40199208405027 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2629 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2159 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2629 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2159 / 192 : ℚ) : ℝ) ≤ ((20099604202515 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2629 : ((2825879 / 4503599627370496 : ℚ) : ℝ) ≤ logKernel ((2629 / 64 : ℚ) : ℝ) ∧
    logKernel ((2629 / 64 : ℚ) : ℝ) ≤ ((45214069 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2629
  constructor
  · exact (show ((2825879 / 4503599627370496 : ℚ) : ℝ) ≤ zKernel ((40199208405027 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2629 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((20099604202515 / 9223372036854775808 : ℚ) : ℝ) ≤ ((45214069 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2630 : ((39575977445187 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1315 / 32 : ℚ) : ℝ) ∧
    heightZ ((1315 / 32 : ℚ) : ℝ) ≤ ((19787988722595 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((39575977445187 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1315 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1081 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1315 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1081 / 96 : ℚ) : ℝ) ≤ ((19787988722595 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2630 : ((43822973 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1315 / 32 : ℚ) : ℝ) ∧
    logKernel ((1315 / 32 : ℚ) : ℝ) ≤ ((21911489 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2630
  constructor
  · exact (show ((43822973 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((39575977445187 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1315 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((19787988722595 / 9223372036854775808 : ℚ) : ℝ) ≤ ((21911489 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2631 : ((38962408785793 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2631 / 64 : ℚ) : ℝ) ∧
    heightZ ((2631 / 64 : ℚ) : ℝ) ≤ ((9740602196449 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((38962408785793 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2631 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2165 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2631 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2165 / 192 : ℚ) : ℝ) ≤ ((9740602196449 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2631 : ((21237341 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2631 / 64 : ℚ) : ℝ) ∧
    logKernel ((2631 / 64 : ℚ) : ℝ) ≤ ((42474687 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2631
  constructor
  · exact (show ((21237341 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((38962408785793 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2631 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((9740602196449 / 4611686018427387904 : ℚ) : ℝ) ≤ ((42474687 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2632 : ((38358352626761 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((329 / 8 : ℚ) : ℝ) ∧
    heightZ ((329 / 8 : ℚ) : ℝ) ≤ ((9589588156691 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((38358352626761 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((329 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-271 / 24 : ℚ) : ℝ) ∧
      Real.exp (-((329 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-271 / 24 : ℚ) : ℝ) ≤ ((9589588156691 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2632 : ((20583937 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((329 / 8 : ℚ) : ℝ) ∧
    logKernel ((329 / 8 : ℚ) : ℝ) ≤ ((41167879 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2632
  constructor
  · exact (show ((20583937 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((38358352626761 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((329 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((9589588156691 / 4611686018427387904 : ℚ) : ℝ) ≤ ((41167879 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2633 : ((37763661490443 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2633 / 64 : ℚ) : ℝ) ∧
    heightZ ((2633 / 64 : ℚ) : ℝ) ≤ ((18881830745223 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((37763661490443 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2633 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2171 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2633 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2171 / 192 : ℚ) : ℝ) ≤ ((18881830745223 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2633 : ((39901271 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2633 / 64 : ℚ) : ℝ) ∧
    logKernel ((2633 / 64 : ℚ) : ℝ) ≤ ((9975319 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2633
  constructor
  · exact (show ((39901271 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((37763661490443 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2633 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((18881830745223 / 9223372036854775808 : ℚ) : ℝ) ≤ ((9975319 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2634 : ((9294547546405 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((1317 / 32 : ℚ) : ℝ) ∧
    heightZ ((1317 / 32 : ℚ) : ℝ) ≤ ((37178190185623 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((9294547546405 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((1317 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1087 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1317 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1087 / 96 : ℚ) : ℝ) ≤ ((37178190185623 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2634 : ((19336819 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((1317 / 32 : ℚ) : ℝ) ∧
    logKernel ((1317 / 32 : ℚ) : ℝ) ≤ ((38673643 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2634
  constructor
  · exact (show ((19336819 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((9294547546405 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1317 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((37178190185623 / 18446744073709551616 : ℚ) : ℝ) ≤ ((38673643 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2635 : ((9150448943013 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((2635 / 64 : ℚ) : ℝ) ∧
    heightZ ((2635 / 64 : ℚ) : ℝ) ≤ ((36601795772055 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((9150448943013 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((2635 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2177 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2635 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2177 / 192 : ℚ) : ℝ) ≤ ((36601795772055 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2635 : ((37483775 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2635 / 64 : ℚ) : ℝ) ∧
    logKernel ((2635 / 64 : ℚ) : ℝ) ≤ ((9370945 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2635
  constructor
  · exact (show ((37483775 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((9150448943013 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2635 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((36601795772055 / 18446744073709551616 : ℚ) : ℝ) ≤ ((9370945 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2636 : ((36034337525585 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((659 / 16 : ℚ) : ℝ) ∧
    heightZ ((659 / 16 : ℚ) : ℝ) ≤ ((9008584381397 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((36034337525585 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((659 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-545 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((659 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-545 / 48 : ℚ) : ℝ) ≤ ((9008584381397 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2636 : ((36330521 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((659 / 16 : ℚ) : ℝ) ∧
    logKernel ((659 / 16 : ℚ) : ℝ) ≤ ((18165263 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2636
  constructor
  · exact (show ((36330521 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((36034337525585 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((659 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((9008584381397 / 4611686018427387904 : ℚ) : ℝ) ≤ ((18165263 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2637 : ((35475676903789 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2637 / 64 : ℚ) : ℝ) ∧
    heightZ ((2637 / 64 : ℚ) : ℝ) ≤ ((2217229806487 / 1152921504606846976 : ℚ) : ℝ) := by
  have h : ((35475676903789 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2637 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2183 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2637 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2183 / 192 : ℚ) : ℝ) ≤ ((2217229806487 / 1152921504606846976 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2637 : ((8803187 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((2637 / 64 : ℚ) : ℝ) ∧
    logKernel ((2637 / 64 : ℚ) : ℝ) ≤ ((35212753 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2637
  constructor
  · exact (show ((8803187 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((35475676903789 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2637 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((2217229806487 / 1152921504606846976 : ℚ) : ℝ) ≤ ((35212753 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2638 : ((34925677512135 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1319 / 32 : ℚ) : ℝ) ∧
    heightZ ((1319 / 32 : ℚ) : ℝ) ≤ ((17462838756069 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((34925677512135 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1319 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1093 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1319 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1093 / 96 : ℚ) : ℝ) ≤ ((17462838756069 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2638 : ((34129365 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1319 / 32 : ℚ) : ℝ) ∧
    logKernel ((1319 / 32 : ℚ) : ℝ) ≤ ((17064685 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2638
  constructor
  · exact (show ((34129365 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((34925677512135 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1319 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((17462838756069 / 9223372036854775808 : ℚ) : ℝ) ≤ ((17064685 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2639 : ((34384205070697 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2639 / 64 : ℚ) : ℝ) ∧
    heightZ ((2639 / 64 : ℚ) : ℝ) ≤ ((8596051267675 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((34384205070697 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2639 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2189 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2639 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2189 / 192 : ℚ) : ℝ) ≤ ((8596051267675 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2639 : ((33079315 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2639 / 64 : ℚ) : ℝ) ∧
    logKernel ((2639 / 64 : ℚ) : ℝ) ≤ ((4134915 / 9007199254740992 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2639
  constructor
  · exact (show ((33079315 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((34384205070697 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2639 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((8596051267675 / 4611686018427387904 : ℚ) : ℝ) ≤ ((4134915 / 9007199254740992 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2640 : ((8462781845341 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((165 / 4 : ℚ) : ℝ) ∧
    heightZ ((165 / 4 : ℚ) : ℝ) ≤ ((33851127381367 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((8462781845341 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((165 / 4 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-137 / 12 : ℚ) : ℝ) ∧
      Real.exp (-((165 / 4 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-137 / 12 : ℚ) : ℝ) ≤ ((33851127381367 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2640 : ((8015393 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((165 / 4 : ℚ) : ℝ) ∧
    logKernel ((165 / 4 : ℚ) : ℝ) ≤ ((32061577 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2640
  constructor
  · exact (show ((8015393 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((8462781845341 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((165 / 4 : ℚ) : ℝ)) hh).trans
      (show zKernel ((33851127381367 / 18446744073709551616 : ℚ) : ℝ) ≤ ((32061577 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

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

theorem log_height_bounds_768 : ((267205585523436287 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1305 / 32 : ℚ) : ℝ) ∧
    Real.log ((1305 / 32 : ℚ) : ℝ) ≤ ((133602792761718145 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((267205585523436287 / 72057594037927936 : ℚ) : ℝ) ≤ ((1305 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1305 / 32 : ℚ) : ℝ) ≤ Real.exp ((133602792761718145 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_768 : heightPower (768 : Fin 988) ≤ ((3475891539091437 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_768
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_768 : heightFactor (768 : Fin 988) ≤ ((2071061833 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_768
  obtain ⟨hpl, hph⟩ := kernel_bounds_2609
  obtain ⟨hcl, hch⟩ := kernel_bounds_2610
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2610
  have h : (((1703025 / 512 : ℚ) : ℝ) * (logKernel ((2609 / 64 : ℚ) : ℝ) - logKernel ((1305 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1305 / 32 : ℚ) : ℝ) + Real.log ((1305 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((2071061833 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_769 : ((133616594254711647 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2611 / 64 : ℚ) : ℝ) ∧
    Real.log ((2611 / 64 : ℚ) : ℝ) ≤ ((267233188509423297 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((133616594254711647 / 36028797018963968 : ℚ) : ℝ) ≤ ((2611 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2611 / 64 : ℚ) : ℝ) ≤ Real.exp ((267233188509423297 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_769 : heightPower (769 : Fin 988) ≤ ((435049676220819 / 35184372088832 : ℚ) : ℝ) := by
  have hh := log_height_bounds_769
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_769 : heightFactor (769 : Fin 988) ≤ ((2019630157 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_769
  obtain ⟨hpl, hph⟩ := kernel_bounds_2610
  obtain ⟨hcl, hch⟩ := kernel_bounds_2611
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2611
  have h : (((6817321 / 2048 : ℚ) : ℝ) * (logKernel ((1305 / 32 : ℚ) : ℝ) - logKernel ((2611 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2611 / 64 : ℚ) : ℝ) + Real.log ((2611 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((2019630157 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_770 : ((133630390462813965 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((653 / 16 : ℚ) : ℝ) ∧
    Real.log ((653 / 16 : ℚ) : ℝ) ≤ ((267260780925627933 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((133630390462813965 / 36028797018963968 : ℚ) : ℝ) ≤ ((653 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((653 / 16 : ℚ) : ℝ) ≤ Real.exp ((267260780925627933 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_770 : heightPower (770 : Fin 988) ≤ ((217806452447091 / 17592186044416 : ℚ) : ℝ) := by
  have hh := log_height_bounds_770
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_770 : heightFactor (770 : Fin 988) ≤ ((1969475075 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_770
  obtain ⟨hpl, hph⟩ := kernel_bounds_2611
  obtain ⟨hcl, hch⟩ := kernel_bounds_2612
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2612
  have h : (((426409 / 128 : ℚ) : ℝ) * (logKernel ((2611 / 64 : ℚ) : ℝ) - logKernel ((653 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((653 / 16 : ℚ) : ℝ) + Real.log ((653 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1969475075 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_771 : ((133644181390070947 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2613 / 64 : ℚ) : ℝ) ∧
    Real.log ((2613 / 64 : ℚ) : ℝ) ≤ ((267288362780141897 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((133644181390070947 / 36028797018963968 : ℚ) : ℝ) ≤ ((2613 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2613 / 64 : ℚ) : ℝ) ≤ Real.exp ((267288362780141897 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_771 : heightPower (771 : Fin 988) ≤ ((3489409027283755 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_771
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_771 : heightFactor (771 : Fin 988) ≤ ((1920564917 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_771
  obtain ⟨hpl, hph⟩ := kernel_bounds_2612
  obtain ⟨hcl, hch⟩ := kernel_bounds_2613
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2613
  have h : (((6827769 / 2048 : ℚ) : ℝ) * (logKernel ((653 / 16 : ℚ) : ℝ) - logKernel ((2613 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2613 / 64 : ℚ) : ℝ) + Real.log ((2613 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1920564917 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_772 : ((133657967040523799 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((1307 / 32 : ℚ) : ℝ) ∧
    Real.log ((1307 / 32 : ℚ) : ℝ) ≤ ((267315934081047601 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((133657967040523799 / 36028797018963968 : ℚ) : ℝ) ≤ ((1307 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1307 / 32 : ℚ) : ℝ) ≤ Real.exp ((267315934081047601 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_772 : heightPower (772 : Fin 988) ≤ ((1746957387094511 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_772
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_772 : heightFactor (772 : Fin 988) ≤ ((29263575 / 4398046511104 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_772
  obtain ⟨hpl, hph⟩ := kernel_bounds_2613
  obtain ⟨hcl, hch⟩ := kernel_bounds_2614
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2614
  have h : (((1708249 / 512 : ℚ) : ℝ) * (logKernel ((2613 / 64 : ℚ) : ℝ) - logKernel ((1307 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1307 / 32 : ℚ) : ℝ) + Real.log ((1307 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((29263575 / 4398046511104 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_773 : ((66835873709104545 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((2615 / 64 : ℚ) : ℝ) ∧
    Real.log ((2615 / 64 : ℚ) : ℝ) ≤ ((267343494836418183 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((66835873709104545 / 18014398509481984 : ℚ) : ℝ) ≤ ((2615 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2615 / 64 : ℚ) : ℝ) ≤ Real.exp ((267343494836418183 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_773 : heightPower (773 : Fin 988) ≤ ((437302559987599 / 35184372088832 : ℚ) : ℝ) := by
  have hh := log_height_bounds_773
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_773 : heightFactor (773 : Fin 988) ≤ ((1826356605 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_773
  obtain ⟨hpl, hph⟩ := kernel_bounds_2614
  obtain ⟨hcl, hch⟩ := kernel_bounds_2615
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2615
  have h : (((6838225 / 2048 : ℚ) : ℝ) * (logKernel ((1307 / 32 : ℚ) : ℝ) - logKernel ((2615 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2615 / 64 : ℚ) : ℝ) + Real.log ((2615 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1826356605 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_774 : ((267371045054317517 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((327 / 8 : ℚ) : ℝ) ∧
    Real.log ((327 / 8 : ℚ) : ℝ) ≤ ((16710690315894845 / 4503599627370496 : ℚ) : ℝ) := by
  have hl : Real.exp ((267371045054317517 / 72057594037927936 : ℚ) : ℝ) ≤ ((327 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((327 / 8 : ℚ) : ℝ) ≤ Real.exp ((16710690315894845 / 4503599627370496 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_774 : heightPower (774 : Fin 988) ≤ ((3502926144450565 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_774
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_774 : heightFactor (774 : Fin 988) ≤ ((1780998961 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_774
  obtain ⟨hpl, hph⟩ := kernel_bounds_2615
  obtain ⟨hcl, hch⟩ := kernel_bounds_2616
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2616
  have h : (((106929 / 32 : ℚ) : ℝ) * (logKernel ((2615 / 64 : ℚ) : ℝ) - logKernel ((327 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((327 / 8 : ℚ) : ℝ) + Real.log ((327 / 8 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1780998961 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_775 : ((16712411546425015 / 4503599627370496 : ℚ) : ℝ) ≤ Real.log ((2617 / 64 : ℚ) : ℝ) ∧
    Real.log ((2617 / 64 : ℚ) : ℝ) ≤ ((267398584742800243 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((16712411546425015 / 4503599627370496 : ℚ) : ℝ) ≤ ((2617 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2617 / 64 : ℚ) : ℝ) ≤ Real.exp ((267398584742800243 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_775 : heightPower (775 : Fin 988) ≤ ((3507431767869805 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_775
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_775 : heightFactor (775 : Fin 988) ≤ ((217095903 / 35184372088832 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_775
  obtain ⟨hpl, hph⟩ := kernel_bounds_2616
  obtain ⟨hcl, hch⟩ := kernel_bounds_2617
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2617
  have h : (((6848689 / 2048 : ℚ) : ℝ) * (logKernel ((327 / 8 : ℚ) : ℝ) - logKernel ((2617 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2617 / 64 : ℚ) : ℝ) + Real.log ((2617 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((217095903 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_776 : ((66856528477477937 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((1309 / 32 : ℚ) : ℝ) ∧
    Real.log ((1309 / 32 : ℚ) : ℝ) ≤ ((267426113909911751 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((66856528477477937 / 18014398509481984 : ℚ) : ℝ) ≤ ((1309 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1309 / 32 : ℚ) : ℝ) ≤ Real.exp ((267426113909911751 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_776 : heightPower (776 : Fin 988) ≤ ((1755968675094969 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_776
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_776 : heightFactor (776 : Fin 988) ≤ ((846816731 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_776
  obtain ⟨hpl, hph⟩ := kernel_bounds_2617
  obtain ⟨hcl, hch⟩ := kernel_bounds_2618
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2618
  have h : (((1713481 / 512 : ℚ) : ℝ) * (logKernel ((2617 / 64 : ℚ) : ℝ) - logKernel ((1309 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1309 / 32 : ℚ) : ℝ) + Real.log ((1309 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((846816731 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_777 : ((267453632563688225 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2619 / 64 : ℚ) : ℝ) ∧
    Real.log ((2619 / 64 : ℚ) : ℝ) ≤ ((66863408140922057 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((267453632563688225 / 72057594037927936 : ℚ) : ℝ) ≤ ((2619 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2619 / 64 : ℚ) : ℝ) ≤ Real.exp ((66863408140922057 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_777 : heightPower (777 : Fin 988) ≤ ((3516442891442357 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_777
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_777 : heightFactor (777 : Fin 988) ≤ ((1651570433 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_777
  obtain ⟨hpl, hph⟩ := kernel_bounds_2618
  obtain ⟨hcl, hch⟩ := kernel_bounds_2619
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2619
  have h : (((6859161 / 2048 : ℚ) : ℝ) * (logKernel ((1309 / 32 : ℚ) : ℝ) - logKernel ((2619 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2619 / 64 : ℚ) : ℝ) + Real.log ((2619 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1651570433 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_778 : ((267481140712156649 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((655 / 16 : ℚ) : ℝ) ∧
    Real.log ((655 / 16 : ℚ) : ℝ) ≤ ((66870285178039163 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((267481140712156649 / 72057594037927936 : ℚ) : ℝ) ≤ ((655 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((655 / 16 : ℚ) : ℝ) ≤ Real.exp ((66870285178039163 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_778 : heightPower (778 : Fin 988) ≤ ((3520948391658415 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_778
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_778 : heightFactor (778 : Fin 988) ≤ ((1610551573 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_778
  obtain ⟨hpl, hph⟩ := kernel_bounds_2619
  obtain ⟨hcl, hch⟩ := kernel_bounds_2620
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2620
  have h : (((429025 / 128 : ℚ) : ℝ) * (logKernel ((2619 / 64 : ℚ) : ℝ) - logKernel ((655 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((655 / 16 : ℚ) : ℝ) + Real.log ((655 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1610551573 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_779 : ((267508638363334809 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2621 / 64 : ℚ) : ℝ) ∧
    Real.log ((2621 / 64 : ℚ) : ℝ) ≤ ((66877159590833703 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((267508638363334809 / 72057594037927936 : ℚ) : ℝ) ≤ ((2621 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2621 / 64 : ℚ) : ℝ) ≤ Real.exp ((66877159590833703 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_779 : heightPower (779 : Fin 988) ≤ ((1762726925434717 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_779
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_779 : heightFactor (779 : Fin 988) ≤ ((1570550975 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_779
  obtain ⟨hpl, hph⟩ := kernel_bounds_2620
  obtain ⟨hcl, hch⟩ := kernel_bounds_2621
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2621
  have h : (((6869641 / 2048 : ℚ) : ℝ) * (logKernel ((655 / 16 : ℚ) : ℝ) - logKernel ((2621 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2621 / 64 : ℚ) : ℝ) + Real.log ((2621 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1570550975 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_780 : ((267536125525231319 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1311 / 32 : ℚ) : ℝ) ∧
    Real.log ((1311 / 32 : ℚ) : ℝ) ≤ ((133768062762615661 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((267536125525231319 / 72057594037927936 : ℚ) : ℝ) ≤ ((1311 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1311 / 32 : ℚ) : ℝ) ≤ Real.exp ((133768062762615661 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_780 : heightPower (780 : Fin 988) ≤ ((441244908638337 / 35184372088832 : ℚ) : ℝ) := by
  have hh := log_height_bounds_780
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_780 : heightFactor (780 : Fin 988) ≤ ((1531543375 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_780
  obtain ⟨hpl, hph⟩ := kernel_bounds_2621
  obtain ⟨hcl, hch⟩ := kernel_bounds_2622
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2622
  have h : (((1718721 / 512 : ℚ) : ℝ) * (logKernel ((2621 / 64 : ℚ) : ℝ) - logKernel ((1311 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1311 / 32 : ℚ) : ℝ) + Real.log ((1311 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1531543375 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_781 : ((2090340642233169 / 562949953421312 : ℚ) : ℝ) ≤ Real.log ((2623 / 64 : ℚ) : ℝ) ∧
    Real.log ((2623 / 64 : ℚ) : ℝ) ≤ ((267563602205845635 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((2090340642233169 / 562949953421312 : ℚ) : ℝ) ≤ ((2623 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2623 / 64 : ℚ) : ℝ) ≤ Real.exp ((267563602205845635 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_781 : heightPower (781 : Fin 988) ≤ ((1767232323200725 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_781
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_781 : heightFactor (781 : Fin 988) ≤ ((1493504137 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_781
  obtain ⟨hpl, hph⟩ := kernel_bounds_2622
  obtain ⟨hcl, hch⟩ := kernel_bounds_2623
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2623
  have h : (((6880129 / 2048 : ℚ) : ℝ) * (logKernel ((1311 / 32 : ℚ) : ℝ) - logKernel ((2623 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2623 / 64 : ℚ) : ℝ) + Real.log ((2623 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1493504137 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_782 : ((66897767103292013 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((41 / 1 : ℚ) : ℝ) ∧
    Real.log ((41 / 1 : ℚ) : ℝ) ≤ ((267591068413168055 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((66897767103292013 / 18014398509481984 : ℚ) : ℝ) ≤ ((41 / 1 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((41 / 1 : ℚ) : ℝ) ≤ Real.exp ((267591068413168055 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_782 : heightPower (782 : Fin 988) ≤ ((3538969982784907 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_782
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_782 : heightFactor (782 : Fin 988) ≤ ((1456409233 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_782
  obtain ⟨hpl, hph⟩ := kernel_bounds_2623
  obtain ⟨hcl, hch⟩ := kernel_bounds_2624
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2624
  have h : (((3362 / 1 : ℚ) : ℝ) * (logKernel ((2623 / 64 : ℚ) : ℝ) - logKernel ((41 / 1 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((41 / 1 : ℚ) : ℝ) + Real.log ((41 / 1 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1456409233 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_783 : ((267618524155179751 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2625 / 64 : ℚ) : ℝ) ∧
    Real.log ((2625 / 64 : ℚ) : ℝ) ≤ ((133809262077589877 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((267618524155179751 / 72057594037927936 : ℚ) : ℝ) ≤ ((2625 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2625 / 64 : ℚ) : ℝ) ≤ Real.exp ((133809262077589877 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_783 : heightPower (783 : Fin 988) ≤ ((885868819572061 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_783
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_783 : heightFactor (783 : Fin 988) ≤ ((44382351 / 8796093022208 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_783
  obtain ⟨hpl, hph⟩ := kernel_bounds_2624
  obtain ⟨hcl, hch⟩ := kernel_bounds_2625
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2625
  have h : (((6890625 / 2048 : ℚ) : ℝ) * (logKernel ((41 / 1 : ℚ) : ℝ) - logKernel ((2625 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2625 / 64 : ℚ) : ℝ) + Real.log ((2625 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((44382351 / 8796093022208 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_784 : ((133822984719926391 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((1313 / 32 : ℚ) : ℝ) ∧
    Real.log ((1313 / 32 : ℚ) : ℝ) ≤ ((267645969439852785 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((133822984719926391 / 36028797018963968 : ℚ) : ℝ) ≤ ((1313 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1313 / 32 : ℚ) : ℝ) ≤ Real.exp ((267645969439852785 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_784 : heightPower (784 : Fin 988) ≤ ((1773990266471301 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_784
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_784 : heightFactor (784 : Fin 988) ≤ ((692479643 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_784
  obtain ⟨hpl, hph⟩ := kernel_bounds_2625
  obtain ⟨hcl, hch⟩ := kernel_bounds_2626
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2626
  have h : (((1723969 / 512 : ℚ) : ℝ) * (logKernel ((2625 / 64 : ℚ) : ℝ) - logKernel ((1313 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1313 / 32 : ℚ) : ℝ) + Real.log ((1313 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((692479643 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_785 : ((267673404275150089 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2627 / 64 : ℚ) : ℝ) ∧
    Real.log ((2627 / 64 : ℚ) : ℝ) ≤ ((66918351068787523 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((267673404275150089 / 72057594037927936 : ℚ) : ℝ) ≤ ((2627 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2627 / 64 : ℚ) : ℝ) ≤ Real.exp ((66918351068787523 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_785 : heightPower (785 : Fin 988) ≤ ((3552485746779087 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_785
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_785 : heightFactor (785 : Fin 988) ≤ ((1350559111 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_785
  obtain ⟨hpl, hph⟩ := kernel_bounds_2626
  obtain ⟨hcl, hch⟩ := kernel_bounds_2627
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2627
  have h : (((6901129 / 2048 : ℚ) : ℝ) * (logKernel ((1313 / 32 : ℚ) : ℝ) - logKernel ((2627 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2627 / 64 : ℚ) : ℝ) + Real.log ((2627 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1350559111 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_786 : ((33462603583628191 / 9007199254740992 : ℚ) : ℝ) ≤ Real.log ((657 / 16 : ℚ) : ℝ) ∧
    Real.log ((657 / 16 : ℚ) : ℝ) ≤ ((267700828669025531 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((33462603583628191 / 9007199254740992 : ℚ) : ℝ) ≤ ((657 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((657 / 16 : ℚ) : ℝ) ≤ Real.exp ((267700828669025531 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_786 : heightPower (786 : Fin 988) ≤ ((1778495459914383 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_786
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_786 : heightFactor (786 : Fin 988) ≤ ((82313311 / 17592186044416 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_786
  obtain ⟨hpl, hph⟩ := kernel_bounds_2627
  obtain ⟨hcl, hch⟩ := kernel_bounds_2628
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2628
  have h : (((431649 / 128 : ℚ) : ℝ) * (logKernel ((2627 / 64 : ℚ) : ℝ) - logKernel ((657 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((657 / 16 : ℚ) : ℝ) + Real.log ((657 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((82313311 / 17592186044416 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_787 : ((133864121314711937 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2629 / 64 : ℚ) : ℝ) ∧
    Real.log ((2629 / 64 : ℚ) : ℝ) ≤ ((267728242629423877 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((133864121314711937 / 36028797018963968 : ℚ) : ℝ) ≤ ((2629 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2629 / 64 : ℚ) : ℝ) ≤ Real.exp ((267728242629423877 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_787 : heightPower (787 : Fin 988) ≤ ((3561496052122677 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_787
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_787 : heightFactor (787 : Fin 988) ≤ ((642149845 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_787
  obtain ⟨hpl, hph⟩ := kernel_bounds_2628
  obtain ⟨hcl, hch⟩ := kernel_bounds_2629
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2629
  have h : (((6911641 / 2048 : ℚ) : ℝ) * (logKernel ((657 / 16 : ℚ) : ℝ) - logKernel ((2629 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2629 / 64 : ℚ) : ℝ) + Real.log ((2629 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((642149845 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_788 : ((33469455770535105 / 9007199254740992 : ℚ) : ℝ) ≤ Real.log ((1315 / 32 : ℚ) : ℝ) ∧
    Real.log ((1315 / 32 : ℚ) : ℝ) ≤ ((267755646164280843 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((33469455770535105 / 9007199254740992 : ℚ) : ℝ) ≤ ((1315 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1315 / 32 : ℚ) : ℝ) ≤ Real.exp ((267755646164280843 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_788 : heightPower (788 : Fin 988) ≤ ((445750142961477 / 35184372088832 : ℚ) : ℝ) := by
  have hh := log_height_bounds_788
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_788 : heightFactor (788 : Fin 988) ≤ ((1252398587 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_788
  obtain ⟨hpl, hph⟩ := kernel_bounds_2629
  obtain ⟨hcl, hch⟩ := kernel_bounds_2630
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2630
  have h : (((1729225 / 512 : ℚ) : ℝ) * (logKernel ((2629 / 64 : ℚ) : ℝ) - logKernel ((1315 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1315 / 32 : ℚ) : ℝ) + Real.log ((1315 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1252398587 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_789 : ((16736439955095193 / 4503599627370496 : ℚ) : ℝ) ≤ Real.log ((2631 / 64 : ℚ) : ℝ) ∧
    Real.log ((2631 / 64 : ℚ) : ℝ) ≤ ((267783039281523091 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((16736439955095193 / 4503599627370496 : ℚ) : ℝ) ≤ ((2631 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2631 / 64 : ℚ) : ℝ) ≤ Real.exp ((267783039281523091 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_789 : heightPower (789 : Fin 988) ≤ ((3570506194567147 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_789
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_789 : heightFactor (789 : Fin 988) ≤ ((610644757 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_789
  obtain ⟨hpl, hph⟩ := kernel_bounds_2630
  obtain ⟨hcl, hch⟩ := kernel_bounds_2631
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2631
  have h : (((6922161 / 2048 : ℚ) : ℝ) * (logKernel ((1315 / 32 : ℚ) : ℝ) - logKernel ((2631 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2631 / 64 : ℚ) : ℝ) + Real.log ((2631 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((610644757 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_790 : ((133905210994534121 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((329 / 8 : ℚ) : ℝ) ∧
    Real.log ((329 / 8 : ℚ) : ℝ) ≤ ((267810421989068245 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((133905210994534121 / 36028797018963968 : ℚ) : ℝ) ≤ ((329 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((329 / 8 : ℚ) : ℝ) ≤ Real.exp ((267810421989068245 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_790 : heightPower (790 : Fin 988) ≤ ((3575011204779599 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_790
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_790 : heightFactor (790 : Fin 988) ≤ ((74434551 / 17592186044416 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_790
  obtain ⟨hpl, hph⟩ := kernel_bounds_2631
  obtain ⟨hcl, hch⟩ := kernel_bounds_2632
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2632
  have h : (((108241 / 32 : ℚ) : ℝ) * (logKernel ((2631 / 64 : ℚ) : ℝ) - logKernel ((329 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((329 / 8 : ℚ) : ℝ) + Real.log ((329 / 8 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((74434551 / 17592186044416 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_791 : ((267837794294824905 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2633 / 64 : ℚ) : ℝ) ∧
    Real.log ((2633 / 64 : ℚ) : ℝ) ≤ ((66959448573706227 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((267837794294824905 / 72057594037927936 : ℚ) : ℝ) ≤ ((2633 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2633 / 64 : ℚ) : ℝ) ≤ Real.exp ((66959448573706227 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_791 : heightPower (791 : Fin 988) ≤ ((3579516174360065 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_791
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_791 : heightFactor (791 : Fin 988) ≤ ((72585583 / 17592186044416 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_791
  obtain ⟨hpl, hph⟩ := kernel_bounds_2632
  obtain ⟨hcl, hch⟩ := kernel_bounds_2633
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2633
  have h : (((6932689 / 2048 : ℚ) : ℝ) * (logKernel ((329 / 8 : ℚ) : ℝ) - logKernel ((2633 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2633 / 64 : ℚ) : ℝ) + Real.log ((2633 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((72585583 / 17592186044416 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_792 : ((267865156206692669 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1317 / 32 : ℚ) : ℝ) ∧
    Real.log ((1317 / 32 : ℚ) : ℝ) ≤ ((4185393065729573 / 1125899906842624 : ℚ) : ℝ) := by
  have hl : Real.exp ((267865156206692669 / 72057594037927936 : ℚ) : ℝ) ≤ ((1317 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1317 / 32 : ℚ) : ℝ) ≤ Real.exp ((4185393065729573 / 1125899906842624 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_792 : heightPower (792 : Fin 988) ≤ ((3584021103339403 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_792
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_792 : heightFactor (792 : Fin 988) ≤ ((1132520359 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_792
  obtain ⟨hpl, hph⟩ := kernel_bounds_2633
  obtain ⟨hcl, hch⟩ := kernel_bounds_2634
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2634
  have h : (((1734489 / 512 : ℚ) : ℝ) * (logKernel ((2633 / 64 : ℚ) : ℝ) - logKernel ((1317 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1317 / 32 : ℚ) : ℝ) + Real.log ((1317 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1132520359 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_793 : ((267892507732562131 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2635 / 64 : ℚ) : ℝ) ∧
    Real.log ((2635 / 64 : ℚ) : ℝ) ≤ ((133946253866281067 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((267892507732562131 / 72057594037927936 : ℚ) : ℝ) ≤ ((2635 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2635 / 64 : ℚ) : ℝ) ≤ Real.exp ((133946253866281067 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_793 : heightPower (793 : Fin 988) ≤ ((1794262995874217 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_793
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_793 : heightFactor (793 : Fin 988) ≤ ((34512115 / 8796093022208 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_793
  obtain ⟨hpl, hph⟩ := kernel_bounds_2634
  obtain ⟨hcl, hch⟩ := kernel_bounds_2635
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2635
  have h : (((6943225 / 2048 : ℚ) : ℝ) * (logKernel ((1317 / 32 : ℚ) : ℝ) - logKernel ((2635 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2635 / 64 : ℚ) : ℝ) + Real.log ((2635 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((34512115 / 8796093022208 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_794 : ((66979962220078727 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((659 / 16 : ℚ) : ℝ) ∧
    Real.log ((659 / 16 : ℚ) : ℝ) ≤ ((267919848880314911 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((66979962220078727 / 18014398509481984 : ℚ) : ℝ) ≤ ((659 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((659 / 16 : ℚ) : ℝ) ≤ Real.exp ((267919848880314911 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_794 : heightPower (794 : Fin 988) ≤ ((898257709904487 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_794
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_794 : heightFactor (794 : Fin 988) ≤ ((538476759 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_794
  obtain ⟨hpl, hph⟩ := kernel_bounds_2635
  obtain ⟨hcl, hch⟩ := kernel_bounds_2636
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2636
  have h : (((434281 / 128 : ℚ) : ℝ) * (logKernel ((2635 / 64 : ℚ) : ℝ) - logKernel ((659 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((659 / 16 : ℚ) : ℝ) + Real.log ((659 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((538476759 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_795 : ((133973589828911823 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2637 / 64 : ℚ) : ℝ) ∧
    Real.log ((2637 / 64 : ℚ) : ℝ) ≤ ((267947179657823649 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((133973589828911823 / 36028797018963968 : ℚ) : ℝ) ≤ ((2637 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2637 / 64 : ℚ) : ℝ) ≤ Real.exp ((267947179657823649 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_795 : heightPower (795 : Fin 988) ≤ ((3597535646978695 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_795
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_795 : heightFactor (795 : Fin 988) ≤ ((1050200537 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_795
  obtain ⟨hpl, hph⟩ := kernel_bounds_2636
  obtain ⟨hcl, hch⟩ := kernel_bounds_2637
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2637
  have h : (((6953769 / 2048 : ℚ) : ℝ) * (logKernel ((659 / 16 : ℚ) : ℝ) - logKernel ((2637 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2637 / 64 : ℚ) : ℝ) + Real.log ((2637 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1050200537 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_796 : ((267974500072952037 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1319 / 32 : ℚ) : ℝ) ∧
    Real.log ((1319 / 32 : ℚ) : ℝ) ≤ ((33496812509119005 / 9007199254740992 : ℚ) : ℝ) := by
  have hl : Real.exp ((267974500072952037 / 72057594037927936 : ℚ) : ℝ) ≤ ((1319 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1319 / 32 : ℚ) : ℝ) ≤ Real.exp ((33496812509119005 / 9007199254740992 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_796 : heightPower (796 : Fin 988) ≤ ((1801020206930697 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_796
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_796 : heightFactor (796 : Fin 988) ≤ ((512055917 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_796
  obtain ⟨hpl, hph⟩ := kernel_bounds_2637
  obtain ⟨hcl, hch⟩ := kernel_bounds_2638
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2638
  have h : (((1739761 / 512 : ℚ) : ℝ) * (logKernel ((2637 / 64 : ℚ) : ℝ) - logKernel ((1319 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1319 / 32 : ℚ) : ℝ) + Real.log ((1319 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((512055917 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_797 : ((268001810133554833 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2639 / 64 : ℚ) : ℝ) ∧
    Real.log ((2639 / 64 : ℚ) : ℝ) ≤ ((67000452533388709 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((268001810133554833 / 72057594037927936 : ℚ) : ℝ) ≤ ((2639 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2639 / 64 : ℚ) : ℝ) ≤ Real.exp ((67000452533388709 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_797 : heightPower (797 : Fin 988) ≤ ((450818142537091 / 35184372088832 : ℚ) : ℝ) := by
  have hh := log_height_bounds_797
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_797 : heightFactor (797 : Fin 988) ≤ ((499335461 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_797
  obtain ⟨hpl, hph⟩ := kernel_bounds_2638
  obtain ⟨hcl, hch⟩ := kernel_bounds_2639
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2639
  have h : (((6964321 / 2048 : ℚ) : ℝ) * (logKernel ((1319 / 32 : ℚ) : ℝ) - logKernel ((2639 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2639 / 64 : ℚ) : ℝ) + Real.log ((2639 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((499335461 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_798 : ((134014554923738929 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((165 / 4 : ℚ) : ℝ) ∧
    Real.log ((165 / 4 : ℚ) : ℝ) ≤ ((268029109847477861 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((134014554923738929 / 36028797018963968 : ℚ) : ℝ) ≤ ((165 / 4 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((165 / 4 : ℚ) : ℝ) ≤ Real.exp ((268029109847477861 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_798 : heightPower (798 : Fin 988) ≤ ((225690614144709 / 17592186044416 : ℚ) : ℝ) := by
  have hh := log_height_bounds_798
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_798 : heightFactor (798 : Fin 988) ≤ ((973861725 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_798
  obtain ⟨hpl, hph⟩ := kernel_bounds_2639
  obtain ⟨hcl, hch⟩ := kernel_bounds_2640
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2640
  have h : (((27225 / 8 : ℚ) : ℝ) * (logKernel ((2639 / 64 : ℚ) : ℝ) - logKernel ((165 / 4 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((165 / 4 : ℚ) : ℝ) + Real.log ((165 / 4 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((973861725 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_799 : ((134028199611279011 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2641 / 64 : ℚ) : ℝ) ∧
    Real.log ((2641 / 64 : ℚ) : ℝ) ≤ ((268056399222558025 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((134028199611279011 / 36028797018963968 : ℚ) : ℝ) ≤ ((2641 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2641 / 64 : ℚ) : ℝ) ≤ Real.exp ((268056399222558025 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_799 : heightPower (799 : Fin 988) ≤ ((3615554471947855 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_799
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_799 : heightFactor (799 : Fin 988) ≤ ((949668567 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_799
  obtain ⟨hpl, hph⟩ := kernel_bounds_2640
  obtain ⟨hcl, hch⟩ := kernel_bounds_2641
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2641
  have h : (((6974881 / 2048 : ℚ) : ℝ) * (logKernel ((165 / 4 : ℚ) : ℝ) - logKernel ((2641 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2641 / 64 : ℚ) : ℝ) + Real.log ((2641 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((949668567 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

end LegendreK6.M2Pilot.Enclosures.Height024
