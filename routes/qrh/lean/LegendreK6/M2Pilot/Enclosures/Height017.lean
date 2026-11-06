import LegendreK6.M2PilotDefinitions
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp

/-! Generated proposals: every bound is checked by Lean, not by trusting Arb. -/
namespace LegendreK6.M2Pilot.Enclosures.Height017
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem height_z_bounds_2385 : ((1819555107961295 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2385 / 64 : ℚ) : ℝ) ∧
    heightZ ((2385 / 64 : ℚ) : ℝ) ≤ ((909777553980649 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((1819555107961295 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2385 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1427 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2385 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1427 / 192 : ℚ) : ℝ) ≤ ((909777553980649 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2385 : ((23158424039 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((2385 / 64 : ℚ) : ℝ) ∧
    logKernel ((2385 / 64 : ℚ) : ℝ) ≤ ((92633696161 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2385
  constructor
  · exact (show ((23158424039 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((1819555107961295 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2385 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((909777553980649 / 9223372036854775808 : ℚ) : ℝ) ≤ ((92633696161 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2386 : ((895672760361443 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((1193 / 32 : ℚ) : ℝ) ∧
    heightZ ((1193 / 32 : ℚ) : ℝ) ≤ ((1791345520722889 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((895672760361443 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((1193 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-715 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1193 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-715 / 96 : ℚ) : ℝ) ≤ ((1791345520722889 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2386 : ((44891828473 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((1193 / 32 : ℚ) : ℝ) ∧
    logKernel ((1193 / 32 : ℚ) : ℝ) ≤ ((89783656951 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2386
  constructor
  · exact (show ((44891828473 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((895672760361443 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1193 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1791345520722889 / 18446744073709551616 : ℚ) : ℝ) ≤ ((89783656951 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2387 : ((1763573282597279 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2387 / 64 : ℚ) : ℝ) ∧
    heightZ ((2387 / 64 : ℚ) : ℝ) ≤ ((881786641298641 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((1763573282597279 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2387 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1433 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2387 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1433 / 192 : ℚ) : ℝ) ≤ ((881786641298641 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2387 : ((87021304225 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2387 / 64 : ℚ) : ℝ) ∧
    logKernel ((2387 / 64 : ℚ) : ℝ) ≤ ((43510652115 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2387
  constructor
  · exact (show ((87021304225 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((1763573282597279 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2387 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((881786641298641 / 9223372036854775808 : ℚ) : ℝ) ≤ ((43510652115 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2388 : ((868115806557477 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((597 / 16 : ℚ) : ℝ) ∧
    heightZ ((597 / 16 : ℚ) : ℝ) ≤ ((1736231613114957 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((868115806557477 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((597 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-359 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((597 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-359 / 48 : ℚ) : ℝ) ≤ ((1736231613114957 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2388 : ((42171970081 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((597 / 16 : ℚ) : ℝ) ∧
    logKernel ((597 / 16 : ℚ) : ℝ) ≤ ((84343940167 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2388
  constructor
  · exact (show ((42171970081 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((868115806557477 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((597 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1736231613114957 / 18446744073709551616 : ℚ) : ℝ) ≤ ((84343940167 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2389 : ((1709313836927825 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2389 / 64 : ℚ) : ℝ) ∧
    heightZ ((2389 / 64 : ℚ) : ℝ) ≤ ((427328459231957 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((1709313836927825 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2389 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1439 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2389 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1439 / 192 : ℚ) : ℝ) ≤ ((427328459231957 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2389 : ((20437237483 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((2389 / 64 : ℚ) : ℝ) ∧
    logKernel ((2389 / 64 : ℚ) : ℝ) ≤ ((81748949937 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2389
  constructor
  · exact (show ((20437237483 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((1709313836927825 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2389 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((427328459231957 / 4611686018427387904 : ℚ) : ℝ) ≤ ((81748949937 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2390 : ((1682813382179487 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1195 / 32 : ℚ) : ℝ) ∧
    heightZ ((1195 / 32 : ℚ) : ℝ) ≤ ((841406691089745 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((1682813382179487 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1195 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-721 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1195 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-721 / 96 : ℚ) : ℝ) ≤ ((841406691089745 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2390 : ((39616899579 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((1195 / 32 : ℚ) : ℝ) ∧
    logKernel ((1195 / 32 : ℚ) : ℝ) ≤ ((79233799163 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2390
  constructor
  · exact (show ((39616899579 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((1682813382179487 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1195 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((841406691089745 / 9223372036854775808 : ℚ) : ℝ) ≤ ((79233799163 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2391 : ((828361889450363 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2391 / 64 : ℚ) : ℝ) ∧
    heightZ ((2391 / 64 : ℚ) : ℝ) ≤ ((1656723778900729 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((828361889450363 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2391 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1445 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2391 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1445 / 192 : ℚ) : ℝ) ≤ ((1656723778900729 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2391 : ((76796031437 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2391 / 64 : ℚ) : ℝ) ∧
    logKernel ((2391 / 64 : ℚ) : ℝ) ≤ ((38398015721 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2391
  constructor
  · exact (show ((76796031437 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((828361889450363 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2391 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1656723778900729 / 18446744073709551616 : ℚ) : ℝ) ≤ ((38398015721 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2392 : ((407759664357475 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((299 / 8 : ℚ) : ℝ) ∧
    heightZ ((299 / 8 : ℚ) : ℝ) ≤ ((1631038657429903 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((407759664357475 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((299 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-181 / 24 : ℚ) : ℝ) ∧
      Real.exp (-((299 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-181 / 24 : ℚ) : ℝ) ≤ ((1631038657429903 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2392 : ((74433265945 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((299 / 8 : ℚ) : ℝ) ∧
    logKernel ((299 / 8 : ℚ) : ℝ) ≤ ((37216632975 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2392
  constructor
  · exact (show ((74433265945 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((407759664357475 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((299 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1631038657429903 / 18446744073709551616 : ℚ) : ℝ) ≤ ((37216632975 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2393 : ((802875873428911 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2393 / 64 : ℚ) : ℝ) ∧
    heightZ ((2393 / 64 : ℚ) : ℝ) ≤ ((1605751746857825 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((802875873428911 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2393 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1451 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2393 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1451 / 192 : ℚ) : ℝ) ≤ ((1605751746857825 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2393 : ((2254474847 / 2251799813685248 : ℚ) : ℝ) ≤ logKernel ((2393 / 64 : ℚ) : ℝ) ∧
    logKernel ((2393 / 64 : ℚ) : ℝ) ≤ ((72143195109 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2393
  constructor
  · exact (show ((2254474847 / 2251799813685248 : ℚ) : ℝ) ≤ zKernel ((802875873428911 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2393 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1605751746857825 / 18446744073709551616 : ℚ) : ℝ) ≤ ((72143195109 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2394 : ((49401777296773 / 576460752303423488 : ℚ) : ℝ) ≤ heightZ ((1197 / 32 : ℚ) : ℝ) ∧
    heightZ ((1197 / 32 : ℚ) : ℝ) ≤ ((1580856873496739 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((49401777296773 / 576460752303423488 : ℚ) : ℝ) ≤ Real.exp (-((1197 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-727 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1197 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-727 / 96 : ℚ) : ℝ) ≤ ((1580856873496739 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2394 : ((546277987 / 562949953421312 : ℚ) : ℝ) ≤ logKernel ((1197 / 32 : ℚ) : ℝ) ∧
    logKernel ((1197 / 32 : ℚ) : ℝ) ≤ ((69923582341 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2394
  constructor
  · exact (show ((546277987 / 562949953421312 : ℚ) : ℝ) ≤ zKernel ((49401777296773 / 576460752303423488 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1197 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1580856873496739 / 18446744073709551616 : ℚ) : ℝ) ≤ ((69923582341 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2395 : ((778173979686523 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2395 / 64 : ℚ) : ℝ) ∧
    heightZ ((2395 / 64 : ℚ) : ℝ) ≤ ((1556347959373049 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((778173979686523 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2395 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1457 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2395 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1457 / 192 : ℚ) : ℝ) ≤ ((1556347959373049 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2395 : ((33886129937 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2395 / 64 : ℚ) : ℝ) ∧
    logKernel ((2395 / 64 : ℚ) : ℝ) ≤ ((67772259879 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2395
  constructor
  · exact (show ((33886129937 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((778173979686523 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2395 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1556347959373049 / 18446744073709551616 : ℚ) : ℝ) ≤ ((67772259879 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2396 : ((766109510371701 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((599 / 16 : ℚ) : ℝ) ∧
    heightZ ((599 / 16 : ℚ) : ℝ) ≤ ((1532219020743405 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((766109510371701 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((599 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-365 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((599 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-365 / 48 : ℚ) : ℝ) ≤ ((1532219020743405 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2396 : ((65687126645 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((599 / 16 : ℚ) : ℝ) ∧
    logKernel ((599 / 16 : ℚ) : ℝ) ≤ ((32843563325 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2396
  constructor
  · exact (show ((65687126645 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((766109510371701 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((599 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1532219020743405 / 18446744073709551616 : ℚ) : ℝ) ≤ ((32843563325 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2397 : ((1508464166633795 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2397 / 64 : ℚ) : ℝ) ∧
    heightZ ((2397 / 64 : ℚ) : ℝ) ≤ ((754232083316899 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((1508464166633795 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2397 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1463 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2397 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1463 / 192 : ℚ) : ℝ) ≤ ((754232083316899 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2397 : ((31833073111 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2397 / 64 : ℚ) : ℝ) ∧
    logKernel ((2397 / 64 : ℚ) : ℝ) ≤ ((63666146227 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2397
  constructor
  · exact (show ((31833073111 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((1508464166633795 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2397 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((754232083316899 / 9223372036854775808 : ℚ) : ℝ) ≤ ((63666146227 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2398 : ((185634699675163 / 2305843009213693952 : ℚ) : ℝ) ≤ heightZ ((1199 / 32 : ℚ) : ℝ) ∧
    heightZ ((1199 / 32 : ℚ) : ℝ) ≤ ((1485077597401307 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((185634699675163 / 2305843009213693952 : ℚ) : ℝ) ≤ Real.exp (-((1199 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-733 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1199 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-733 / 96 : ℚ) : ℝ) ≤ ((1485077597401307 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2398 : ((61707344829 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1199 / 32 : ℚ) : ℝ) ∧
    logKernel ((1199 / 32 : ℚ) : ℝ) ≤ ((30853672417 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2398
  constructor
  · exact (show ((61707344829 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((185634699675163 / 2305843009213693952 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1199 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1485077597401307 / 18446744073709551616 : ℚ) : ℝ) ≤ ((30853672417 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2399 : ((182756700414767 / 2305843009213693952 : ℚ) : ℝ) ≤ heightZ ((2399 / 64 : ℚ) : ℝ) ∧
    heightZ ((2399 / 64 : ℚ) : ℝ) ≤ ((1462053603318139 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((182756700414767 / 2305843009213693952 : ℚ) : ℝ) ≤ Real.exp (-((2399 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1469 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2399 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1469 / 192 : ℚ) : ℝ) ≤ ((1462053603318139 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2399 : ((14952202355 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((2399 / 64 : ℚ) : ℝ) ∧
    logKernel ((2399 / 64 : ℚ) : ℝ) ≤ ((59808809425 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2399
  constructor
  · exact (show ((14952202355 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((182756700414767 / 2305843009213693952 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2399 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1462053603318139 / 18446744073709551616 : ℚ) : ℝ) ≤ ((59808809425 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2400 : ((179923320397203 / 2305843009213693952 : ℚ) : ℝ) ≤ heightZ ((75 / 2 : ℚ) : ℝ) ∧
    heightZ ((75 / 2 : ℚ) : ℝ) ≤ ((1439386563177627 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((179923320397203 / 2305843009213693952 : ℚ) : ℝ) ≤ Real.exp (-((75 / 2 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-23 / 3 : ℚ) : ℝ) ∧
      Real.exp (-((75 / 2 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-23 / 3 : ℚ) : ℝ) ≤ ((1439386563177627 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2400 : ((14492171451 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((75 / 2 : ℚ) : ℝ) ∧
    logKernel ((75 / 2 : ℚ) : ℝ) ≤ ((57968685809 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2400
  constructor
  · exact (show ((14492171451 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((179923320397203 / 2305843009213693952 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((75 / 2 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1439386563177627 / 18446744073709551616 : ℚ) : ℝ) ≤ ((57968685809 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2401 : ((1417070942921831 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2401 / 64 : ℚ) : ℝ) ∧
    heightZ ((2401 / 64 : ℚ) : ℝ) ≤ ((708535471460917 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((1417070942921831 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2401 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1475 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2401 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1475 / 192 : ℚ) : ℝ) ≤ ((708535471460917 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2401 : ((7023147105 / 9007199254740992 : ℚ) : ℝ) ≤ logKernel ((2401 / 64 : ℚ) : ℝ) ∧
    logKernel ((2401 / 64 : ℚ) : ℝ) ≤ ((56185176845 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2401
  constructor
  · exact (show ((7023147105 / 9007199254740992 : ℚ) : ℝ) ≤ zKernel ((1417070942921831 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2401 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((708535471460917 / 9223372036854775808 : ℚ) : ℝ) ≤ ((56185176845 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2402 : ((1395101294290437 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1201 / 32 : ℚ) : ℝ) ∧
    heightZ ((1201 / 32 : ℚ) : ℝ) ≤ ((174387661786305 / 2305843009213693952 : ℚ) : ℝ) := by
  have h : ((1395101294290437 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1201 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-739 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1201 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-739 / 96 : ℚ) : ℝ) ≤ ((174387661786305 / 2305843009213693952 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2402 : ((27228270339 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((1201 / 32 : ℚ) : ℝ) ∧
    logKernel ((1201 / 32 : ℚ) : ℝ) ≤ ((54456540683 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2402
  constructor
  · exact (show ((27228270339 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((1395101294290437 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1201 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((174387661786305 / 2305843009213693952 : ℚ) : ℝ) ≤ ((54456540683 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2403 : ((1373472253490569 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2403 / 64 : ℚ) : ℝ) ∧
    heightZ ((2403 / 64 : ℚ) : ℝ) ≤ ((343368063372643 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((1373472253490569 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2403 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1481 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2403 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1481 / 192 : ℚ) : ℝ) ≤ ((343368063372643 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2403 : ((13195272265 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((2403 / 64 : ℚ) : ℝ) ∧
    logKernel ((2403 / 64 : ℚ) : ℝ) ≤ ((52781089065 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2403
  constructor
  · exact (show ((13195272265 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((1373472253490569 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2403 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((343368063372643 / 4611686018427387904 : ℚ) : ℝ) ≤ ((52781089065 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2404 : ((676089269943627 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((601 / 16 : ℚ) : ℝ) ∧
    heightZ ((601 / 16 : ℚ) : ℝ) ≤ ((1352178539887257 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((676089269943627 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((601 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-371 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((601 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-371 / 48 : ℚ) : ℝ) ≤ ((1352178539887257 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2404 : ((12789296417 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((601 / 16 : ℚ) : ℝ) ∧
    logKernel ((601 / 16 : ℚ) : ℝ) ≤ ((51157185673 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2404
  constructor
  · exact (show ((12789296417 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((676089269943627 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((601 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1352178539887257 / 18446744073709551616 : ℚ) : ℝ) ≤ ((51157185673 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2405 : ((1331214954714177 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2405 / 64 : ℚ) : ℝ) ∧
    heightZ ((2405 / 64 : ℚ) : ℝ) ≤ ((332803738678545 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((1331214954714177 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2405 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1487 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2405 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1487 / 192 : ℚ) : ℝ) ≤ ((332803738678545 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2405 : ((12395811133 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((2405 / 64 : ℚ) : ℝ) ∧
    logKernel ((2405 / 64 : ℚ) : ℝ) ≤ ((49583244537 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2405
  constructor
  · exact (show ((12395811133 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((1331214954714177 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2405 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((332803738678545 / 4611686018427387904 : ℚ) : ℝ) ≤ ((49583244537 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2406 : ((163822047475553 / 2305843009213693952 : ℚ) : ℝ) ≤ heightZ ((1203 / 32 : ℚ) : ℝ) ∧
    heightZ ((1203 / 32 : ℚ) : ℝ) ≤ ((1310576379804427 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((163822047475553 / 2305843009213693952 : ℚ) : ℝ) ≤ Real.exp (-((1203 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-745 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1203 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-745 / 96 : ℚ) : ℝ) ≤ ((1310576379804427 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2406 : ((24028864237 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((1203 / 32 : ℚ) : ℝ) ∧
    logKernel ((1203 / 32 : ℚ) : ℝ) ≤ ((48057728479 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2406
  constructor
  · exact (show ((24028864237 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((163822047475553 / 2305843009213693952 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1203 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1310576379804427 / 18446744073709551616 : ℚ) : ℝ) ≤ ((48057728479 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2407 : ((645128888170451 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2407 / 64 : ℚ) : ℝ) ∧
    heightZ ((2407 / 64 : ℚ) : ℝ) ≤ ((1290257776340905 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((645128888170451 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2407 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1493 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2407 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1493 / 192 : ℚ) : ℝ) ≤ ((1290257776340905 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2407 : ((23289573805 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2407 / 64 : ℚ) : ℝ) ∧
    logKernel ((2407 / 64 : ℚ) : ℝ) ≤ ((46579147615 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2407
  constructor
  · exact (show ((23289573805 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((645128888170451 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2407 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1290257776340905 / 18446744073709551616 : ℚ) : ℝ) ≤ ((46579147615 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2408 : ((1270254183626139 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((301 / 8 : ℚ) : ℝ) ∧
    heightZ ((301 / 8 : ℚ) : ℝ) ≤ ((635127091813071 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((1270254183626139 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((301 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-187 / 24 : ℚ) : ℝ) ∧
      Real.exp (-((301 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-187 / 24 : ℚ) : ℝ) ≤ ((635127091813071 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2408 : ((45146057897 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((301 / 8 : ℚ) : ℝ) ∧
    logKernel ((301 / 8 : ℚ) : ℝ) ≤ ((22573028951 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2408
  constructor
  · exact (show ((45146057897 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((1270254183626139 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((301 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((635127091813071 / 9223372036854775808 : ℚ) : ℝ) ≤ ((22573028951 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2409 : ((312640179467787 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((2409 / 64 : ℚ) : ℝ) ∧
    heightZ ((2409 / 64 : ℚ) : ℝ) ≤ ((1250560717871151 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((312640179467787 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((2409 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1499 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2409 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1499 / 192 : ℚ) : ℝ) ≤ ((1250560717871151 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2409 : ((43757059719 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2409 / 64 : ℚ) : ℝ) ∧
    logKernel ((2409 / 64 : ℚ) : ℝ) ≤ ((10939264931 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2409
  constructor
  · exact (show ((43757059719 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((312640179467787 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2409 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1250560717871151 / 18446744073709551616 : ℚ) : ℝ) ≤ ((10939264931 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2410 : ((1231172571003071 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1205 / 32 : ℚ) : ℝ) ∧
    heightZ ((1205 / 32 : ℚ) : ℝ) ≤ ((615586285501537 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((1231172571003071 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1205 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-751 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1205 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-751 / 96 : ℚ) : ℝ) ≤ ((615586285501537 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2410 : ((42410796523 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1205 / 32 : ℚ) : ℝ) ∧
    logKernel ((1205 / 32 : ℚ) : ℝ) ≤ ((2650674783 / 4503599627370496 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2410
  constructor
  · exact (show ((42410796523 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((1231172571003071 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1205 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((615586285501537 / 9223372036854775808 : ℚ) : ℝ) ≤ ((2650674783 / 4503599627370496 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2411 : ((1212085009491311 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2411 / 64 : ℚ) : ℝ) ∧
    heightZ ((2411 / 64 : ℚ) : ℝ) ≤ ((606042504745657 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((1212085009491311 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2411 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1505 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2411 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1505 / 192 : ℚ) : ℝ) ≤ ((606042504745657 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2411 : ((41105953491 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2411 / 64 : ℚ) : ℝ) ∧
    logKernel ((2411 / 64 : ℚ) : ℝ) ≤ ((5138244187 / 9007199254740992 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2411
  constructor
  · exact (show ((41105953491 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((1212085009491311 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2411 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((606042504745657 / 9223372036854775808 : ℚ) : ℝ) ≤ ((5138244187 / 9007199254740992 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2412 : ((596646686595931 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((603 / 16 : ℚ) : ℝ) ∧
    heightZ ((603 / 16 : ℚ) : ℝ) ≤ ((1193293373191865 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((596646686595931 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((603 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-377 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((603 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-377 / 48 : ℚ) : ℝ) ≤ ((1193293373191865 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2412 : ((19920628129 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((603 / 16 : ℚ) : ℝ) ∧
    logKernel ((603 / 16 : ℚ) : ℝ) ≤ ((39841256263 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2412
  constructor
  · exact (show ((19920628129 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((596646686595931 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((603 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1193293373191865 / 18446744073709551616 : ℚ) : ℝ) ≤ ((39841256263 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2413 : ((587396537104777 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2413 / 64 : ℚ) : ℝ) ∧
    heightZ ((2413 / 64 : ℚ) : ℝ) ≤ ((1174793074209557 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((587396537104777 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2413 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1511 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2413 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1511 / 192 : ℚ) : ℝ) ≤ ((1174793074209557 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2413 : ((9653867417 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((2413 / 64 : ℚ) : ℝ) ∧
    logKernel ((2413 / 64 : ℚ) : ℝ) ≤ ((38615469673 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2413
  constructor
  · exact (show ((9653867417 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((587396537104777 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2413 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1174793074209557 / 18446744073709551616 : ℚ) : ℝ) ≤ ((38615469673 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2414 : ((72286224736121 / 1152921504606846976 : ℚ) : ℝ) ≤ heightZ ((1207 / 32 : ℚ) : ℝ) ∧
    heightZ ((1207 / 32 : ℚ) : ℝ) ≤ ((1156579595777939 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((72286224736121 / 1152921504606846976 : ℚ) : ℝ) ≤ Real.exp (-((1207 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-757 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1207 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-757 / 96 : ℚ) : ℝ) ≤ ((1156579595777939 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2414 : ((37427396567 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1207 / 32 : ℚ) : ℝ) ∧
    logKernel ((1207 / 32 : ℚ) : ℝ) ≤ ((9356849143 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2414
  constructor
  · exact (show ((37427396567 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((72286224736121 / 1152921504606846976 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1207 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1156579595777939 / 18446744073709551616 : ℚ) : ℝ) ≤ ((9356849143 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2415 : ((1138648491156533 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2415 / 64 : ℚ) : ℝ) ∧
    heightZ ((2415 / 64 : ℚ) : ℝ) ≤ ((142331061394567 / 2305843009213693952 : ℚ) : ℝ) := by
  have h : ((1138648491156533 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2415 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1517 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2415 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1517 / 192 : ℚ) : ℝ) ≤ ((142331061394567 / 2305843009213693952 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2415 : ((36275876633 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2415 / 64 : ℚ) : ℝ) ∧
    logKernel ((2415 / 64 : ℚ) : ℝ) ≤ ((18137938319 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2415
  constructor
  · exact (show ((36275876633 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((1138648491156533 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2415 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((142331061394567 / 2305843009213693952 : ℚ) : ℝ) ≤ ((18137938319 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2416 : ((1120995382545191 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((151 / 4 : ℚ) : ℝ) ∧
    heightZ ((151 / 4 : ℚ) : ℝ) ≤ ((560497691272597 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((1120995382545191 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((151 / 4 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-95 / 12 : ℚ) : ℝ) ∧
      Real.exp (-((151 / 4 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-95 / 12 : ℚ) : ℝ) ≤ ((560497691272597 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2416 : ((17579892621 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((151 / 4 : ℚ) : ℝ) ∧
    logKernel ((151 / 4 : ℚ) : ℝ) ≤ ((35159785247 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2416
  constructor
  · exact (show ((17579892621 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((1120995382545191 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((151 / 4 : ℚ) : ℝ)) hh).trans
      (show zKernel ((560497691272597 / 9223372036854775808 : ℚ) : ℝ) ≤ ((35159785247 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

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

theorem log_height_bounds_544 : ((16296232554354999 / 4503599627370496 : ℚ) : ℝ) ≤ Real.log ((1193 / 32 : ℚ) : ℝ) ∧
    Real.log ((1193 / 32 : ℚ) : ℝ) ≤ ((260739720869679987 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((16296232554354999 / 4503599627370496 : ℚ) : ℝ) ≤ ((1193 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1193 / 32 : ℚ) : ℝ) ≤ Real.exp ((260739720869679987 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_544 : heightPower (544 : Fin 988) ≤ ((2465471836800405 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_544
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_544 : heightFactor (544 : Fin 988) ≤ ((573632423409 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_544
  obtain ⟨hpl, hph⟩ := kernel_bounds_2385
  obtain ⟨hcl, hch⟩ := kernel_bounds_2386
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2386
  have h : (((1423249 / 512 : ℚ) : ℝ) * (logKernel ((2385 / 64 : ℚ) : ℝ) - logKernel ((1193 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1193 / 32 : ℚ) : ℝ) + Real.log ((1193 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((573632423409 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_545 : ((260769914707975503 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2387 / 64 : ℚ) : ℝ) ∧
    Real.log ((2387 / 64 : ℚ) : ℝ) ≤ ((130384957353987753 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((260769914707975503 / 72057594037927936 : ℚ) : ℝ) ≤ ((2387 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2387 / 64 : ℚ) : ℝ) ≤ Real.exp ((130384957353987753 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_545 : heightPower (545 : Fin 988) ≤ ((2469987827992351 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_545
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_545 : heightFactor (545 : Fin 988) ≤ ((559433616051 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_545
  obtain ⟨hpl, hph⟩ := kernel_bounds_2386
  obtain ⟨hcl, hch⟩ := kernel_bounds_2387
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2387
  have h : (((5697769 / 2048 : ℚ) : ℝ) * (logKernel ((1193 / 32 : ℚ) : ℝ) - logKernel ((2387 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2387 / 64 : ℚ) : ℝ) + Real.log ((2387 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((559433616051 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_546 : ((260800095899636811 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((597 / 16 : ℚ) : ℝ) ∧
    Real.log ((597 / 16 : ℚ) : ℝ) ≤ ((130400047949818407 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((260800095899636811 / 72057594037927936 : ℚ) : ℝ) ≤ ((597 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((597 / 16 : ℚ) : ℝ) ≤ Real.exp ((130400047949818407 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_546 : heightPower (546 : Fin 988) ≤ ((1237251884891691 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_546
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_546 : heightFactor (546 : Fin 988) ≤ ((272793020281 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_546
  obtain ⟨hpl, hph⟩ := kernel_bounds_2387
  obtain ⟨hcl, hch⟩ := kernel_bounds_2388
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2388
  have h : (((356409 / 128 : ℚ) : ℝ) * (logKernel ((2387 / 64 : ℚ) : ℝ) - logKernel ((597 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((597 / 16 : ℚ) : ℝ) + Real.log ((597 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((272793020281 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_547 : ((32603783056906689 / 9007199254740992 : ℚ) : ℝ) ≤ Real.log ((2389 / 64 : ℚ) : ℝ) ∧
    Real.log ((2389 / 64 : ℚ) : ℝ) ≤ ((260830264455253515 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((32603783056906689 / 9007199254740992 : ℚ) : ℝ) ≤ ((2389 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2389 / 64 : ℚ) : ℝ) ≤ Real.exp ((260830264455253515 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_547 : heightPower (547 : Fin 988) ≤ ((154938728888429 / 17592186044416 : ℚ) : ℝ) := by
  have hh := log_height_bounds_547
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_547 : heightFactor (547 : Fin 988) ≤ ((8313765849 / 4398046511104 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_547
  obtain ⟨hpl, hph⟩ := kernel_bounds_2388
  obtain ⟨hcl, hch⟩ := kernel_bounds_2389
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2389
  have h : (((5707321 / 2048 : ℚ) : ℝ) * (logKernel ((597 / 16 : ℚ) : ℝ) - logKernel ((2389 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2389 / 64 : ℚ) : ℝ) + Real.log ((2389 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((8313765849 / 4398046511104 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_548 : ((260860420385401915 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1195 / 32 : ℚ) : ℝ) ∧
    Real.log ((1195 / 32 : ℚ) : ℝ) ≤ ((130430210192700959 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((260860420385401915 / 72057594037927936 : ℚ) : ℝ) ≤ ((1195 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1195 / 32 : ℚ) : ℝ) ≤ Real.exp ((130430210192700959 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_548 : heightPower (548 : Fin 988) ≤ ((1241767752664055 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_548
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_548 : heightFactor (548 : Fin 988) ≤ ((518910069259 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_548
  obtain ⟨hpl, hph⟩ := kernel_bounds_2389
  obtain ⟨hcl, hch⟩ := kernel_bounds_2390
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2390
  have h : (((1428025 / 512 : ℚ) : ℝ) * (logKernel ((2389 / 64 : ℚ) : ℝ) - logKernel ((1195 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1195 / 32 : ℚ) : ℝ) + Real.log ((1195 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((518910069259 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_549 : ((260890563700645057 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2391 / 64 : ℚ) : ℝ) ∧
    Real.log ((2391 / 64 : ℚ) : ℝ) ≤ ((65222640925161265 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((260890563700645057 / 72057594037927936 : ℚ) : ℝ) ≤ ((2391 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2391 / 64 : ℚ) : ℝ) ≤ Real.exp ((65222640925161265 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_549 : heightPower (549 : Fin 988) ≤ ((1244025649582191 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_549
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_549 : heightFactor (549 : Fin 988) ≤ ((506064946411 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_549
  obtain ⟨hpl, hph⟩ := kernel_bounds_2390
  obtain ⟨hcl, hch⟩ := kernel_bounds_2391
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2391
  have h : (((5716881 / 2048 : ℚ) : ℝ) * (logKernel ((1195 / 32 : ℚ) : ℝ) - logKernel ((2391 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2391 / 64 : ℚ) : ℝ) + Real.log ((2391 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((506064946411 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_550 : ((130460347205766361 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((299 / 8 : ℚ) : ℝ) ∧
    Real.log ((299 / 8 : ℚ) : ℝ) ≤ ((260920694411532725 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((130460347205766361 / 36028797018963968 : ℚ) : ℝ) ≤ ((299 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((299 / 8 : ℚ) : ℝ) ≤ Real.exp ((260920694411532725 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_550 : heightPower (550 : Fin 988) ≤ ((2492567043764891 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_550
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_550 : heightFactor (550 : Fin 988) ≤ ((123384397727 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_550
  obtain ⟨hpl, hph⟩ := kernel_bounds_2391
  obtain ⟨hcl, hch⟩ := kernel_bounds_2392
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2392
  have h : (((89401 / 32 : ℚ) : ℝ) * (logKernel ((2391 / 64 : ℚ) : ℝ) - logKernel ((299 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((299 / 8 : ℚ) : ℝ) + Real.log ((299 / 8 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((123384397727 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_551 : ((65237703132150367 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((2393 / 64 : ℚ) : ℝ) ∧
    Real.log ((2393 / 64 : ℚ) : ℝ) ≤ ((260950812528601471 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((65237703132150367 / 18014398509481984 : ℚ) : ℝ) ≤ ((2393 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2393 / 64 : ℚ) : ℝ) ≤ Real.exp ((260950812528601471 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_551 : heightPower (551 : Fin 988) ≤ ((2497082739170795 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_551
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_551 : heightFactor (551 : Fin 988) ≤ ((481320146857 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_551
  obtain ⟨hpl, hph⟩ := kernel_bounds_2392
  obtain ⟨hcl, hch⟩ := kernel_bounds_2393
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2393
  have h : (((5726449 / 2048 : ℚ) : ℝ) * (logKernel ((299 / 8 : ℚ) : ℝ) - logKernel ((2393 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2393 / 64 : ℚ) : ℝ) + Real.log ((2393 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((481320146857 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_552 : ((260980918062374645 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1197 / 32 : ℚ) : ℝ) ∧
    Real.log ((1197 / 32 : ℚ) : ℝ) ≤ ((32622614757796831 / 9007199254740992 : ℚ) : ℝ) := by
  have hl : Real.exp ((260980918062374645 / 72057594037927936 : ℚ) : ℝ) ≤ ((1197 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1197 / 32 : ℚ) : ℝ) ≤ Real.exp ((32622614757796831 / 9007199254740992 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_552 : heightPower (552 : Fin 988) ≤ ((78174949544475 / 8796093022208 : ℚ) : ℝ) := by
  have hh := log_height_bounds_552
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_552 : heightFactor (552 : Fin 988) ≤ ((117351238113 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_552
  obtain ⟨hpl, hph⟩ := kernel_bounds_2393
  obtain ⟨hcl, hch⟩ := kernel_bounds_2394
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2394
  have h : (((1432809 / 512 : ℚ) : ℝ) * (logKernel ((2393 / 64 : ℚ) : ℝ) - logKernel ((1197 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1197 / 32 : ℚ) : ℝ) + Real.log ((1197 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((117351238113 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_553 : ((130505505511681209 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2395 / 64 : ℚ) : ℝ) ∧
    Real.log ((2395 / 64 : ℚ) : ℝ) ≤ ((261011011023362421 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((130505505511681209 / 36028797018963968 : ℚ) : ℝ) ≤ ((2395 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2395 / 64 : ℚ) : ℝ) ≤ Real.exp ((261011011023362421 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_553 : heightPower (553 : Fin 988) ≤ ((2506113982563163 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_553
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_553 : heightFactor (553 : Fin 988) ≤ ((457784535175 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_553
  obtain ⟨hpl, hph⟩ := kernel_bounds_2394
  obtain ⟨hcl, hch⟩ := kernel_bounds_2395
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2395
  have h : (((5736025 / 2048 : ℚ) : ℝ) * (logKernel ((1197 / 32 : ℚ) : ℝ) - logKernel ((2395 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2395 / 64 : ℚ) : ℝ) + Real.log ((2395 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((457784535175 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_554 : ((261041091422061791 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((599 / 16 : ℚ) : ℝ) ∧
    Real.log ((599 / 16 : ℚ) : ℝ) ≤ ((130520545711030897 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((261041091422061791 / 72057594037927936 : ℚ) : ℝ) ≤ ((599 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((599 / 16 : ℚ) : ℝ) ≤ Real.exp ((130520545711030897 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_554 : heightPower (554 : Fin 988) ≤ ((1255314765315843 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_554
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_554 : heightFactor (554 : Fin 988) ≤ ((446451607127 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_554
  obtain ⟨hpl, hph⟩ := kernel_bounds_2395
  obtain ⟨hcl, hch⟩ := kernel_bounds_2396
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2396
  have h : (((358801 / 128 : ℚ) : ℝ) * (logKernel ((2395 / 64 : ℚ) : ℝ) - logKernel ((599 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((599 / 16 : ℚ) : ℝ) + Real.log ((599 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((446451607127 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_555 : ((261071159268956627 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2397 / 64 : ℚ) : ℝ) ∧
    Real.log ((2397 / 64 : ℚ) : ℝ) ≤ ((130535579634478315 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((261071159268956627 / 72057594037927936 : ℚ) : ℝ) ≤ ((2397 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2397 / 64 : ℚ) : ℝ) ≤ Real.exp ((130535579634478315 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_555 : heightPower (555 : Fin 988) ≤ ((2515145029669723 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_555
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_555 : heightFactor (555 : Fin 988) ≤ ((108849765117 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_555
  obtain ⟨hpl, hph⟩ := kernel_bounds_2396
  obtain ⟨hcl, hch⟩ := kernel_bounds_2397
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2397
  have h : (((5745609 / 2048 : ℚ) : ℝ) * (logKernel ((599 / 16 : ℚ) : ℝ) - logKernel ((2397 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2397 / 64 : ℚ) : ℝ) + Real.log ((2397 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((108849765117 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_556 : ((261101214574517671 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1199 / 32 : ℚ) : ℝ) ∧
    Real.log ((1199 / 32 : ℚ) : ℝ) ≤ ((130550607287258837 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((261101214574517671 / 72057594037927936 : ℚ) : ℝ) ≤ ((1199 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1199 / 32 : ℚ) : ℝ) ≤ Real.exp ((130550607287258837 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_556 : heightPower (556 : Fin 988) ≤ ((2519660479718175 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_556
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_556 : heightFactor (556 : Fin 988) ≤ ((212309981487 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_556
  obtain ⟨hpl, hph⟩ := kernel_bounds_2397
  obtain ⟨hcl, hch⟩ := kernel_bounds_2398
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2398
  have h : (((1437601 / 512 : ℚ) : ℝ) * (logKernel ((2397 / 64 : ℚ) : ℝ) - logKernel ((1199 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1199 / 32 : ℚ) : ℝ) + Real.log ((1199 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((212309981487 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_557 : ((261131257349202571 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2399 / 64 : ℚ) : ℝ) ∧
    Real.log ((2399 / 64 : ℚ) : ℝ) ≤ ((130565628674601287 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((261131257349202571 / 72057594037927936 : ℚ) : ℝ) ≤ ((2399 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2399 / 64 : ℚ) : ℝ) ≤ Real.exp ((130565628674601287 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_557 : heightPower (557 : Fin 988) ≤ ((631043970204473 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_557
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_557 : heightFactor (557 : Fin 988) ≤ ((414107553697 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_557
  obtain ⟨hpl, hph⟩ := kernel_bounds_2398
  obtain ⟨hcl, hch⟩ := kernel_bounds_2399
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2399
  have h : (((5755201 / 2048 : ℚ) : ℝ) * (logKernel ((1199 / 32 : ℚ) : ℝ) - logKernel ((2399 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2399 / 64 : ℚ) : ℝ) + Real.log ((2399 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((414107553697 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_558 : ((65290321900863975 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((75 / 2 : ℚ) : ℝ) ∧
    Real.log ((75 / 2 : ℚ) : ℝ) ≤ ((261161287603455903 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((65290321900863975 / 18014398509481984 : ℚ) : ℝ) ≤ ((75 / 2 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((75 / 2 : ℚ) : ℝ) ≤ Real.exp ((261161287603455903 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_558 : heightPower (558 : Fin 988) ≤ ((2528691233009673 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_558
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_558 : heightFactor (558 : Fin 988) ≤ ((100963809685 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_558
  obtain ⟨hpl, hph⟩ := kernel_bounds_2399
  obtain ⟨hcl, hch⟩ := kernel_bounds_2400
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2400
  have h : (((5625 / 2 : ℚ) : ℝ) * (logKernel ((2399 / 64 : ℚ) : ℝ) - logKernel ((75 / 2 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((75 / 2 : ℚ) : ℝ) + Real.log ((75 / 2 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((100963809685 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_559 : ((130595652673854589 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2401 / 64 : ℚ) : ℝ) ∧
    Real.log ((2401 / 64 : ℚ) : ℝ) ≤ ((261191305347709181 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((130595652673854589 / 36028797018963968 : ℚ) : ℝ) ≤ ((2401 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2401 / 64 : ℚ) : ℝ) ≤ Real.exp ((261191305347709181 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_559 : heightPower (559 : Fin 988) ≤ ((1266603268167133 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_559
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_559 : heightFactor (559 : Fin 988) ≤ ((393856587131 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_559
  obtain ⟨hpl, hph⟩ := kernel_bounds_2400
  obtain ⟨hcl, hch⟩ := kernel_bounds_2401
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2401
  have h : (((5764801 / 2048 : ℚ) : ℝ) * (logKernel ((75 / 2 : ℚ) : ℝ) - logKernel ((2401 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2401 / 64 : ℚ) : ℝ) + Real.log ((2401 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((393856587131 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_560 : ((130610655296190447 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((1201 / 32 : ℚ) : ℝ) ∧
    Real.log ((1201 / 32 : ℚ) : ℝ) ≤ ((261221310592380897 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((130610655296190447 / 36028797018963968 : ℚ) : ℝ) ≤ ((1201 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1201 / 32 : ℚ) : ℝ) ≤ Real.exp ((261221310592380897 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_560 : heightPower (560 : Fin 988) ≤ ((2537721790832369 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_560
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_560 : heightFactor (560 : Fin 988) ≤ ((24006582925 / 17592186044416 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_560
  obtain ⟨hpl, hph⟩ := kernel_bounds_2401
  obtain ⟨hcl, hch⟩ := kernel_bounds_2402
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2402
  have h : (((1442401 / 512 : ℚ) : ℝ) * (logKernel ((2401 / 64 : ℚ) : ℝ) - logKernel ((1201 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1201 / 32 : ℚ) : ℝ) + Real.log ((1201 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((24006582925 / 17592186044416 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_561 : ((261251303347876527 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2403 / 64 : ℚ) : ℝ) ∧
    Real.log ((2403 / 64 : ℚ) : ℝ) ≤ ((130625651673938265 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((261251303347876527 / 72057594037927936 : ℚ) : ℝ) ≤ ((2403 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2403 / 64 : ℚ) : ℝ) ≤ Real.exp ((130625651673938265 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_561 : heightPower (561 : Fin 988) ≤ ((635559249136157 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_561
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_561 : heightFactor (561 : Fin 988) ≤ ((187297670327 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_561
  obtain ⟨hpl, hph⟩ := kernel_bounds_2402
  obtain ⟨hcl, hch⟩ := kernel_bounds_2403
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2403
  have h : (((5774409 / 2048 : ℚ) : ℝ) * (logKernel ((1201 / 32 : ℚ) : ℝ) - logKernel ((2403 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2403 / 64 : ℚ) : ℝ) + Real.log ((2403 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((187297670327 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_562 : ((261281283624588569 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((601 / 16 : ℚ) : ℝ) ∧
    Real.log ((601 / 16 : ℚ) : ℝ) ≤ ((65320320906147143 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((261281283624588569 / 72057594037927936 : ℚ) : ℝ) ≤ ((601 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((601 / 16 : ℚ) : ℝ) ≤ Real.exp ((65320320906147143 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_562 : heightPower (562 : Fin 988) ≤ ((2546752153511639 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_562
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_562 : heightFactor (562 : Fin 988) ≤ ((365320662753 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_562
  obtain ⟨hpl, hph⟩ := kernel_bounds_2403
  obtain ⟨hcl, hch⟩ := kernel_bounds_2404
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2404
  have h : (((361201 / 128 : ℚ) : ℝ) * (logKernel ((2403 / 64 : ℚ) : ℝ) - logKernel ((601 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((601 / 16 : ℚ) : ℝ) + Real.log ((601 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((365320662753 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_563 : ((130655625716448273 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2405 / 64 : ℚ) : ℝ) ∧
    Real.log ((2405 / 64 : ℚ) : ℝ) ≤ ((261311251432896549 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((130655625716448273 / 36028797018963968 : ℚ) : ℝ) ≤ ((2405 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2405 / 64 : ℚ) : ℝ) ≤ Real.exp ((261311251432896549 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_563 : heightPower (563 : Fin 988) ≤ ((1275633630886973 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_563
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_563 : heightFactor (563 : Fin 988) ≤ ((178137737289 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_563
  obtain ⟨hpl, hph⟩ := kernel_bounds_2404
  obtain ⟨hcl, hch⟩ := kernel_bounds_2405
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2405
  have h : (((5784025 / 2048 : ℚ) : ℝ) * (logKernel ((601 / 16 : ℚ) : ℝ) - logKernel ((2405 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2405 / 64 : ℚ) : ℝ) + Real.log ((2405 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((178137737289 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_564 : ((261341206783167037 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1203 / 32 : ℚ) : ℝ) ∧
    Real.log ((1203 / 32 : ℚ) : ℝ) ≤ ((4083456355986985 / 1125899906842624 : ℚ) : ℝ) := by
  have hl : Real.exp ((261341206783167037 / 72057594037927936 : ℚ) : ℝ) ≤ ((1203 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1203 / 32 : ℚ) : ℝ) ≤ Real.exp ((4083456355986985 / 1125899906842624 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_564 : heightPower (564 : Fin 988) ≤ ((638945580343011 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_564
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_564 : heightFactor (564 : Fin 988) ≤ ((173727050693 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_564
  obtain ⟨hpl, hph⟩ := kernel_bounds_2405
  obtain ⟨hcl, hch⟩ := kernel_bounds_2406
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2406
  have h : (((1447209 / 512 : ℚ) : ℝ) * (logKernel ((2405 / 64 : ℚ) : ℝ) - logKernel ((1203 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1203 / 32 : ℚ) : ℝ) + Real.log ((1203 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((173727050693 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_565 : ((65342787421438425 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((2407 / 64 : ℚ) : ℝ) ∧
    Real.log ((2407 / 64 : ℚ) : ℝ) ≤ ((261371149685753703 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((65342787421438425 / 18014398509481984 : ℚ) : ℝ) ≤ ((2407 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2407 / 64 : ℚ) : ℝ) ≤ Real.exp ((261371149685753703 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_565 : heightPower (565 : Fin 988) ≤ ((2560297332346377 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_565
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_565 : heightFactor (565 : Fin 988) ≤ ((42356376083 / 35184372088832 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_565
  obtain ⟨hpl, hph⟩ := kernel_bounds_2406
  obtain ⟨hcl, hch⟩ := kernel_bounds_2407
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2407
  have h : (((5793649 / 2048 : ℚ) : ℝ) * (logKernel ((1203 / 32 : ℚ) : ℝ) - logKernel ((2407 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2407 / 64 : ℚ) : ℝ) + Real.log ((2407 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((42356376083 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_566 : ((130700540075498645 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((301 / 8 : ℚ) : ℝ) ∧
    Real.log ((301 / 8 : ℚ) : ℝ) ≤ ((261401080150997293 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((130700540075498645 / 36028797018963968 : ℚ) : ℝ) ≤ ((301 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((301 / 8 : ℚ) : ℝ) ≤ Real.exp ((261401080150997293 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_566 : heightPower (566 : Fin 988) ≤ ((2564812294737339 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_566
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_566 : heightFactor (566 : Fin 988) ≤ ((82615199667 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_566
  obtain ⟨hpl, hph⟩ := kernel_bounds_2407
  obtain ⟨hcl, hch⟩ := kernel_bounds_2408
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2408
  have h : (((90601 / 32 : ℚ) : ℝ) * (logKernel ((2407 / 64 : ℚ) : ℝ) - logKernel ((301 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((301 / 8 : ℚ) : ℝ) + Real.log ((301 / 8 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((82615199667 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_567 : ((130715499094612841 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2409 / 64 : ℚ) : ℝ) ∧
    Real.log ((2409 / 64 : ℚ) : ℝ) ≤ ((261430998189225685 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((130715499094612841 / 36028797018963968 : ℚ) : ℝ) ≤ ((2409 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2409 / 64 : ℚ) : ℝ) ≤ Real.exp ((261430998189225685 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_567 : heightPower (567 : Fin 988) ≤ ((321165901073159 / 35184372088832 : ℚ) : ℝ) := by
  have hh := log_height_bounds_567
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_567 : heightFactor (567 : Fin 988) ≤ ((161139103519 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_567
  obtain ⟨hpl, hph⟩ := kernel_bounds_2408
  obtain ⟨hcl, hch⟩ := kernel_bounds_2409
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2409
  have h : (((5803281 / 2048 : ℚ) : ℝ) * (logKernel ((301 / 8 : ℚ) : ℝ) - logKernel ((2409 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2409 / 64 : ℚ) : ℝ) + Real.log ((2409 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((161139103519 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_568 : ((65365225952688473 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((1205 / 32 : ℚ) : ℝ) ∧
    Real.log ((1205 / 32 : ℚ) : ℝ) ≤ ((261460903810753895 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((65365225952688473 / 18014398509481984 : ℚ) : ℝ) ≤ ((1205 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1205 / 32 : ℚ) : ℝ) ≤ Real.exp ((261460903810753895 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_568 : heightPower (568 : Fin 988) ≤ ((2573842073930471 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_568
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_568 : heightFactor (568 : Fin 988) ≤ ((39287262439 / 35184372088832 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_568
  obtain ⟨hpl, hph⟩ := kernel_bounds_2409
  obtain ⟨hcl, hch⟩ := kernel_bounds_2410
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2410
  have h : (((1452025 / 512 : ℚ) : ℝ) * (logKernel ((2409 / 64 : ℚ) : ℝ) - logKernel ((1205 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1205 / 32 : ℚ) : ℝ) + Real.log ((1205 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((39287262439 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_569 : ((65372699256471025 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((2411 / 64 : ℚ) : ℝ) ∧
    Real.log ((2411 / 64 : ℚ) : ℝ) ≤ ((261490797025884103 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((65372699256471025 / 18014398509481984 : ℚ) : ℝ) ≤ ((2411 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2411 / 64 : ℚ) : ℝ) ≤ Real.exp ((261490797025884103 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_569 : heightPower (569 : Fin 988) ≤ ((2578356890813177 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_569
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_569 : heightFactor (569 : Fin 988) ≤ ((76628867177 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_569
  obtain ⟨hpl, hph⟩ := kernel_bounds_2410
  obtain ⟨hcl, hch⟩ := kernel_bounds_2411
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2411
  have h : (((5812921 / 2048 : ℚ) : ℝ) * (logKernel ((1205 / 32 : ℚ) : ℝ) - logKernel ((2411 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2411 / 64 : ℚ) : ℝ) + Real.log ((2411 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((76628867177 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_570 : ((261520677844905667 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((603 / 16 : ℚ) : ℝ) ∧
    Real.log ((603 / 16 : ℚ) : ℝ) ≤ ((130760338922452835 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((261520677844905667 / 72057594037927936 : ℚ) : ℝ) ≤ ((603 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((603 / 16 : ℚ) : ℝ) ≤ Real.exp ((130760338922452835 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_570 : heightPower (570 : Fin 988) ≤ ((161429478704599 / 17592186044416 : ℚ) : ℝ) := by
  have hh := log_height_bounds_570
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_570 : heightFactor (570 : Fin 988) ≤ ((298925430995 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_570
  obtain ⟨hpl, hph⟩ := kernel_bounds_2411
  obtain ⟨hcl, hch⟩ := kernel_bounds_2412
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2412
  have h : (((363609 / 128 : ℚ) : ℝ) * (logKernel ((2411 / 64 : ℚ) : ℝ) - logKernel ((603 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((603 / 16 : ℚ) : ℝ) + Real.log ((603 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((298925430995 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_571 : ((32693818284761895 / 9007199254740992 : ℚ) : ℝ) ≤ Real.log ((2413 / 64 : ℚ) : ℝ) ∧
    Real.log ((2413 / 64 : ℚ) : ℝ) ≤ ((261550546278095163 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((32693818284761895 / 9007199254740992 : ℚ) : ℝ) ≤ ((2413 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2413 / 64 : ℚ) : ℝ) ≤ Real.exp ((261550546278095163 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_571 : heightPower (571 : Fin 988) ≤ ((2587386379351835 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_571
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_571 : heightFactor (571 : Fin 988) ≤ ((36440402929 / 35184372088832 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_571
  obtain ⟨hpl, hph⟩ := kernel_bounds_2412
  obtain ⟨hcl, hch⟩ := kernel_bounds_2413
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2413
  have h : (((5822569 / 2048 : ℚ) : ℝ) * (logKernel ((603 / 16 : ℚ) : ℝ) - logKernel ((2413 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2413 / 64 : ℚ) : ℝ) + Real.log ((2413 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((36440402929 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_572 : ((261580402335716373 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1207 / 32 : ℚ) : ℝ) ∧
    Real.log ((1207 / 32 : ℚ) : ℝ) ≤ ((32697550291964547 / 9007199254740992 : ℚ) : ℝ) := by
  have hl : Real.exp ((261580402335716373 / 72057594037927936 : ℚ) : ℝ) ≤ ((1207 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1207 / 32 : ℚ) : ℝ) ≤ Real.exp ((32697550291964547 / 9007199254740992 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_572 : heightPower (572 : Fin 988) ≤ ((1295950525544011 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_572
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_572 : heightFactor (572 : Fin 988) ≤ ((142152100395 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_572
  obtain ⟨hpl, hph⟩ := kernel_bounds_2413
  obtain ⟨hcl, hch⟩ := kernel_bounds_2414
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2414
  have h : (((1456849 / 512 : ℚ) : ℝ) * (logKernel ((2413 / 64 : ℚ) : ℝ) - logKernel ((1207 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1207 / 32 : ℚ) : ℝ) + Real.log ((1207 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((142152100395 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_573 : ((261610246028020347 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2415 / 64 : ℚ) : ℝ) ∧
    Real.log ((2415 / 64 : ℚ) : ℝ) ≤ ((130805123014010175 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((261610246028020347 / 72057594037927936 : ℚ) : ℝ) ≤ ((2415 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2415 / 64 : ℚ) : ℝ) ≤ Real.exp ((130805123014010175 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_573 : heightPower (573 : Fin 988) ≤ ((649103918630547 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_573
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_573 : heightFactor (573 : Fin 988) ≤ ((277263832647 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_573
  obtain ⟨hpl, hph⟩ := kernel_bounds_2414
  obtain ⟨hcl, hch⟩ := kernel_bounds_2415
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2415
  have h : (((5832225 / 2048 : ℚ) : ℝ) * (logKernel ((1207 / 32 : ℚ) : ℝ) - logKernel ((2415 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2415 / 64 : ℚ) : ℝ) + Real.log ((2415 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((277263832647 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_574 : ((130820038682622695 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((151 / 4 : ℚ) : ℝ) ∧
    Real.log ((151 / 4 : ℚ) : ℝ) ≤ ((261640077365245393 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((130820038682622695 / 36028797018963968 : ℚ) : ℝ) ≤ ((151 / 4 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((151 / 4 : ℚ) : ℝ) ≤ Real.exp ((261640077365245393 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_574 : heightPower (574 : Fin 988) ≤ ((2600930249694327 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_574
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_574 : heightFactor (574 : Fin 988) ≤ ((135198850273 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_574
  obtain ⟨hpl, hph⟩ := kernel_bounds_2415
  obtain ⟨hcl, hch⟩ := kernel_bounds_2416
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2416
  have h : (((22801 / 8 : ℚ) : ℝ) * (logKernel ((2415 / 64 : ℚ) : ℝ) - logKernel ((151 / 4 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((151 / 4 : ℚ) : ℝ) + Real.log ((151 / 4 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((135198850273 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_575 : ((261669896357617101 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2417 / 64 : ℚ) : ℝ) ∧
    Real.log ((2417 / 64 : ℚ) : ℝ) ≤ ((16354368522351069 / 4503599627370496 : ℚ) : ℝ) := by
  have hl : Real.exp ((261669896357617101 / 72057594037927936 : ℚ) : ℝ) ≤ ((2417 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2417 / 64 : ℚ) : ℝ) ≤ Real.exp ((16354368522351069 / 4503599627370496 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_575 : heightPower (575 : Fin 988) ≤ ((2605444776644383 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_575
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_575 : heightFactor (575 : Fin 988) ≤ ((263701495239 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_575
  obtain ⟨hpl, hph⟩ := kernel_bounds_2416
  obtain ⟨hcl, hch⟩ := kernel_bounds_2417
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2417
  have h : (((5841889 / 2048 : ℚ) : ℝ) * (logKernel ((151 / 4 : ℚ) : ℝ) - logKernel ((2417 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2417 / 64 : ℚ) : ℝ) + Real.log ((2417 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((263701495239 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

end LegendreK6.M2Pilot.Enclosures.Height017
