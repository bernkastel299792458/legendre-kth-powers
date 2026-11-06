import LegendreK6.M2PilotDefinitions
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp

/-! Generated proposals: every bound is checked by Lean, not by trusting Arb. -/
namespace LegendreK6.M2Pilot.Enclosures.Height029
set_option maxRecDepth 100000
set_option maxHeartbeats 0

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

theorem height_z_bounds_2770 : ((1110075402163 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((1385 / 32 : ℚ) : ℝ) ∧
    heightZ ((1385 / 32 : ℚ) : ℝ) ≤ ((4440301608655 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((1110075402163 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((1385 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1291 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1385 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1291 / 96 : ℚ) : ℝ) ≤ ((4440301608655 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2770 : ((551647 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1385 / 32 : ℚ) : ℝ) ∧
    logKernel ((1385 / 32 : ℚ) : ℝ) ≤ ((137913 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2770
  constructor
  · exact (show ((551647 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((1110075402163 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1385 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((4440301608655 / 18446744073709551616 : ℚ) : ℝ) ≤ ((137913 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2771 : ((4371461112947 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2771 / 64 : ℚ) : ℝ) ∧
    heightZ ((2771 / 64 : ℚ) : ℝ) ≤ ((2185730556475 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((4371461112947 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2771 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2585 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2771 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2585 / 192 : ℚ) : ℝ) ≤ ((2185730556475 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2771 : ((534675 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2771 / 64 : ℚ) : ℝ) ∧
    logKernel ((2771 / 64 : ℚ) : ℝ) ≤ ((66835 / 9007199254740992 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2771
  constructor
  · exact (show ((534675 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((4371461112947 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2771 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((2185730556475 / 9223372036854775808 : ℚ) : ℝ) ≤ ((66835 / 9007199254740992 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2772 : ((1075921972551 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((693 / 16 : ℚ) : ℝ) ∧
    heightZ ((693 / 16 : ℚ) : ℝ) ≤ ((4303687890207 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((1075921972551 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((693 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-647 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((693 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-647 / 48 : ℚ) : ℝ) ≤ ((4303687890207 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2772 : ((518225 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((693 / 16 : ℚ) : ℝ) ∧
    logKernel ((693 / 16 : ℚ) : ℝ) ≤ ((259115 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2772
  constructor
  · exact (show ((518225 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((1075921972551 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((693 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((4303687890207 / 18446744073709551616 : ℚ) : ℝ) ≤ ((259115 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2773 : ((4236965393889 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2773 / 64 : ℚ) : ℝ) ∧
    heightZ ((2773 / 64 : ℚ) : ℝ) ≤ ((1059241348473 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((4236965393889 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2773 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2591 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2773 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2591 / 192 : ℚ) : ℝ) ≤ ((1059241348473 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2773 : ((62785 / 9007199254740992 : ℚ) : ℝ) ≤ logKernel ((2773 / 64 : ℚ) : ℝ) ∧
    logKernel ((2773 / 64 : ℚ) : ℝ) ≤ ((502285 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2773
  constructor
  · exact (show ((62785 / 9007199254740992 : ℚ) : ℝ) ≤ zKernel ((4236965393889 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2773 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1059241348473 / 4611686018427387904 : ℚ) : ℝ) ≤ ((502285 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2774 : ((4171277333999 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1387 / 32 : ℚ) : ℝ) ∧
    heightZ ((1387 / 32 : ℚ) : ℝ) ≤ ((2085638667001 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((4171277333999 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1387 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1297 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1387 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1297 / 96 : ℚ) : ℝ) ≤ ((2085638667001 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2774 : ((486827 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1387 / 32 : ℚ) : ℝ) ∧
    logKernel ((1387 / 32 : ℚ) : ℝ) ≤ ((30427 / 4503599627370496 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2774
  constructor
  · exact (show ((486827 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((4171277333999 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1387 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((2085638667001 / 9223372036854775808 : ℚ) : ℝ) ≤ ((30427 / 4503599627370496 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2775 : ((1026651918271 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((2775 / 64 : ℚ) : ℝ) ∧
    heightZ ((2775 / 64 : ℚ) : ℝ) ≤ ((4106607673087 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((1026651918271 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((2775 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2597 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2775 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2597 / 192 : ℚ) : ℝ) ≤ ((4106607673087 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2775 : ((471849 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2775 / 64 : ℚ) : ℝ) ∧
    logKernel ((2775 / 64 : ℚ) : ℝ) ≤ ((235927 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2775
  constructor
  · exact (show ((471849 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((1026651918271 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2775 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((4106607673087 / 18446744073709551616 : ℚ) : ℝ) ≤ ((235927 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2776 : ((2021470311165 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((347 / 8 : ℚ) : ℝ) ∧
    heightZ ((347 / 8 : ℚ) : ℝ) ≤ ((4042940622333 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((2021470311165 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((347 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-325 / 24 : ℚ) : ℝ) ∧
      Real.exp (-((347 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-325 / 24 : ℚ) : ℝ) ≤ ((4042940622333 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2776 : ((457331 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((347 / 8 : ℚ) : ℝ) ∧
    logKernel ((347 / 8 : ℚ) : ℝ) ≤ ((57167 / 9007199254740992 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2776
  constructor
  · exact (show ((457331 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((2021470311165 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((347 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((4042940622333 / 18446744073709551616 : ℚ) : ℝ) ≤ ((57167 / 9007199254740992 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2777 : ((995065159427 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((2777 / 64 : ℚ) : ℝ) ∧
    heightZ ((2777 / 64 : ℚ) : ℝ) ≤ ((3980260637711 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((995065159427 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((2777 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2603 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2777 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2603 / 192 : ℚ) : ℝ) ≤ ((3980260637711 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2777 : ((443261 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2777 / 64 : ℚ) : ℝ) ∧
    logKernel ((2777 / 64 : ℚ) : ℝ) ≤ ((221633 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2777
  constructor
  · exact (show ((443261 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((995065159427 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2777 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((3980260637711 / 18446744073709551616 : ℚ) : ℝ) ≤ ((221633 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2778 : ((3918552416177 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1389 / 32 : ℚ) : ℝ) ∧
    heightZ ((1389 / 32 : ℚ) : ℝ) ≤ ((979638104045 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((3918552416177 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1389 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1303 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1389 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1303 / 96 : ℚ) : ℝ) ≤ ((979638104045 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2778 : ((429623 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1389 / 32 : ℚ) : ℝ) ∧
    logKernel ((1389 / 32 : ℚ) : ℝ) ≤ ((107407 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2778
  constructor
  · exact (show ((429623 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((3918552416177 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1389 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((979638104045 / 4611686018427387904 : ℚ) : ℝ) ≤ ((107407 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2779 : ((3857800891945 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2779 / 64 : ℚ) : ℝ) ∧
    heightZ ((2779 / 64 : ℚ) : ℝ) ≤ ((964450222987 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((3857800891945 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2779 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2609 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2779 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2609 / 192 : ℚ) : ℝ) ≤ ((964450222987 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2779 : ((416405 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2779 / 64 : ℚ) : ℝ) ∧
    logKernel ((2779 / 64 : ℚ) : ℝ) ≤ ((208205 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2779
  constructor
  · exact (show ((416405 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((3857800891945 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2779 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((964450222987 / 4611686018427387904 : ℚ) : ℝ) ≤ ((208205 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2780 : ((949497808199 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((695 / 16 : ℚ) : ℝ) ∧
    heightZ ((695 / 16 : ℚ) : ℝ) ≤ ((3797991232799 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((949497808199 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((695 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-653 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((695 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-653 / 48 : ℚ) : ℝ) ≤ ((3797991232799 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2780 : ((403593 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((695 / 16 : ℚ) : ℝ) ∧
    logKernel ((695 / 16 : ℚ) : ℝ) ≤ ((201799 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2780
  constructor
  · exact (show ((403593 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((949497808199 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((695 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((3797991232799 / 18446744073709551616 : ℚ) : ℝ) ≤ ((201799 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2781 : ((3739108836465 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2781 / 64 : ℚ) : ℝ) ∧
    heightZ ((2781 / 64 : ℚ) : ℝ) ≤ ((934777209117 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((3739108836465 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2781 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2615 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2781 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2615 / 192 : ℚ) : ℝ) ≤ ((934777209117 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2781 : ((48897 / 9007199254740992 : ℚ) : ℝ) ≤ logKernel ((2781 / 64 : ℚ) : ℝ) ∧
    logKernel ((2781 / 64 : ℚ) : ℝ) ≤ ((391181 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2781
  constructor
  · exact (show ((48897 / 9007199254740992 : ℚ) : ℝ) ≤ zKernel ((3739108836465 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2781 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((934777209117 / 4611686018427387904 : ℚ) : ℝ) ≤ ((391181 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2782 : ((3681139327075 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1391 / 32 : ℚ) : ℝ) ∧
    heightZ ((1391 / 32 : ℚ) : ℝ) ≤ ((1840569663539 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((3681139327075 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1391 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1309 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1391 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1309 / 96 : ℚ) : ℝ) ≤ ((1840569663539 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2782 : ((379141 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1391 / 32 : ℚ) : ℝ) ∧
    logKernel ((1391 / 32 : ℚ) : ℝ) ≤ ((189573 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2782
  constructor
  · exact (show ((379141 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((3681139327075 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1391 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1840569663539 / 9223372036854775808 : ℚ) : ℝ) ≤ ((189573 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2783 : ((1812034275813 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2783 / 64 : ℚ) : ℝ) ∧
    heightZ ((2783 / 64 : ℚ) : ℝ) ≤ ((3624068551629 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((1812034275813 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2783 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2621 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2783 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2621 / 192 : ℚ) : ℝ) ≤ ((3624068551629 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2783 : ((91869 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((2783 / 64 : ℚ) : ℝ) ∧
    logKernel ((2783 / 64 : ℚ) : ℝ) ≤ ((367481 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2783
  constructor
  · exact (show ((91869 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((1812034275813 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2783 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((3624068551629 / 18446744073709551616 : ℚ) : ℝ) ≤ ((367481 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2784 : ((3567882576539 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((87 / 2 : ℚ) : ℝ) ∧
    heightZ ((87 / 2 : ℚ) : ℝ) ≤ ((1783941288271 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((3567882576539 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((87 / 2 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-41 / 3 : ℚ) : ℝ) ∧
      Real.exp (-((87 / 2 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-41 / 3 : ℚ) : ℝ) ≤ ((1783941288271 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2784 : ((356169 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((87 / 2 : ℚ) : ℝ) ∧
    logKernel ((87 / 2 : ℚ) : ℝ) ≤ ((178087 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2784
  constructor
  · exact (show ((356169 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((3567882576539 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((87 / 2 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1783941288271 / 9223372036854775808 : ℚ) : ℝ) ≤ ((178087 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2785 : ((3512567684257 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2785 / 64 : ℚ) : ℝ) ∧
    heightZ ((2785 / 64 : ℚ) : ℝ) ≤ ((878141921065 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((3512567684257 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2785 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2627 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2785 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2627 / 192 : ℚ) : ℝ) ≤ ((878141921065 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2785 : ((345211 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2785 / 64 : ℚ) : ℝ) ∧
    logKernel ((2785 / 64 : ℚ) : ℝ) ≤ ((2697 / 562949953421312 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2785
  constructor
  · exact (show ((345211 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((3512567684257 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2785 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((878141921065 / 4611686018427387904 : ℚ) : ℝ) ≤ ((2697 / 562949953421312 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2786 : ((3458110369891 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1393 / 32 : ℚ) : ℝ) ∧
    heightZ ((1393 / 32 : ℚ) : ℝ) ≤ ((1729055184947 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((3458110369891 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1393 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1315 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1393 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1315 / 96 : ℚ) : ℝ) ≤ ((1729055184947 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2786 : ((167295 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((1393 / 32 : ℚ) : ℝ) ∧
    logKernel ((1393 / 32 : ℚ) : ℝ) ≤ ((334595 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2786
  constructor
  · exact (show ((167295 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((3458110369891 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1393 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1729055184947 / 9223372036854775808 : ℚ) : ℝ) ≤ ((334595 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2787 : ((3404497337929 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2787 / 64 : ℚ) : ℝ) ∧
    heightZ ((2787 / 64 : ℚ) : ℝ) ≤ ((851124334483 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((3404497337929 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2787 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2633 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2787 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2633 / 192 : ℚ) : ℝ) ≤ ((851124334483 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2787 : ((40537 / 9007199254740992 : ℚ) : ℝ) ≤ logKernel ((2787 / 64 : ℚ) : ℝ) ∧
    logKernel ((2787 / 64 : ℚ) : ℝ) ≤ ((324301 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2787
  constructor
  · exact (show ((40537 / 9007199254740992 : ℚ) : ℝ) ≤ zKernel ((3404497337929 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2787 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((851124334483 / 4611686018427387904 : ℚ) : ℝ) ≤ ((324301 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2788 : ((1675857749493 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((697 / 16 : ℚ) : ℝ) ∧
    heightZ ((697 / 16 : ℚ) : ℝ) ≤ ((3351715498989 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((1675857749493 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((697 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-659 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((697 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-659 / 48 : ℚ) : ℝ) ≤ ((3351715498989 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2788 : ((157159 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((697 / 16 : ℚ) : ℝ) ∧
    logKernel ((697 / 16 : ℚ) : ℝ) ≤ ((314323 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2788
  constructor
  · exact (show ((157159 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((1675857749493 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((697 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((3351715498989 / 18446744073709551616 : ℚ) : ℝ) ≤ ((314323 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2789 : ((3299751966607 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2789 / 64 : ℚ) : ℝ) ∧
    heightZ ((2789 / 64 : ℚ) : ℝ) ≤ ((1649875983305 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((3299751966607 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2789 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2639 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2789 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2639 / 192 : ℚ) : ℝ) ≤ ((1649875983305 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2789 : ((304647 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2789 / 64 : ℚ) : ℝ) ∧
    logKernel ((2789 / 64 : ℚ) : ℝ) ≤ ((76163 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2789
  constructor
  · exact (show ((304647 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((3299751966607 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2789 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1649875983305 / 9223372036854775808 : ℚ) : ℝ) ≤ ((76163 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2790 : ((1624297027063 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((1395 / 32 : ℚ) : ℝ) ∧
    heightZ ((1395 / 32 : ℚ) : ℝ) ≤ ((3248594054129 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((1624297027063 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((1395 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1321 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1395 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1321 / 96 : ℚ) : ℝ) ≤ ((3248594054129 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2790 : ((147637 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((1395 / 32 : ℚ) : ℝ) ∧
    logKernel ((1395 / 32 : ℚ) : ℝ) ≤ ((295279 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2790
  constructor
  · exact (show ((147637 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((1624297027063 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1395 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((3248594054129 / 18446744073709551616 : ℚ) : ℝ) ≤ ((295279 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2791 : ((799557317891 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((2791 / 64 : ℚ) : ℝ) ∧
    heightZ ((2791 / 64 : ℚ) : ℝ) ≤ ((3198229271567 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((799557317891 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((2791 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2645 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2791 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2645 / 192 : ℚ) : ℝ) ≤ ((3198229271567 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2791 : ((143095 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2791 / 64 : ℚ) : ℝ) ∧
    logKernel ((2791 / 64 : ℚ) : ℝ) ≤ ((286195 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2791
  constructor
  · exact (show ((143095 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((799557317891 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2791 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((3198229271567 / 18446744073709551616 : ℚ) : ℝ) ≤ ((286195 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2792 : ((3148645322581 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((349 / 8 : ℚ) : ℝ) ∧
    heightZ ((349 / 8 : ℚ) : ℝ) ≤ ((393580665323 / 2305843009213693952 : ℚ) : ℝ) := by
  have h : ((3148645322581 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((349 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-331 / 24 : ℚ) : ℝ) ∧
      Real.exp (-((349 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-331 / 24 : ℚ) : ℝ) ≤ ((393580665323 / 2305843009213693952 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2792 : ((34673 / 9007199254740992 : ℚ) : ℝ) ≤ logKernel ((349 / 8 : ℚ) : ℝ) ∧
    logKernel ((349 / 8 : ℚ) : ℝ) ≤ ((277389 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2792
  constructor
  · exact (show ((34673 / 9007199254740992 : ℚ) : ℝ) ≤ zKernel ((3148645322581 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((349 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((393580665323 / 2305843009213693952 : ℚ) : ℝ) ≤ ((277389 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2793 : ((3099830101475 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2793 / 64 : ℚ) : ℝ) ∧
    heightZ ((2793 / 64 : ℚ) : ℝ) ≤ ((1549915050739 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((3099830101475 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2793 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2651 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2793 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2651 / 192 : ℚ) : ℝ) ≤ ((1549915050739 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2793 : ((134425 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2793 / 64 : ℚ) : ℝ) ∧
    logKernel ((2793 / 64 : ℚ) : ℝ) ≤ ((268855 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2793
  constructor
  · exact (show ((134425 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((3099830101475 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2793 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1549915050739 / 9223372036854775808 : ℚ) : ℝ) ≤ ((268855 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2794 : ((190735730639 / 1152921504606846976 : ℚ) : ℝ) ≤ heightZ ((1397 / 32 : ℚ) : ℝ) ∧
    heightZ ((1397 / 32 : ℚ) : ℝ) ≤ ((3051771690227 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((190735730639 / 1152921504606846976 : ℚ) : ℝ) ≤ Real.exp (-((1397 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1327 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1397 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1327 / 96 : ℚ) : ℝ) ≤ ((3051771690227 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2794 : ((130289 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((1397 / 32 : ℚ) : ℝ) ∧
    logKernel ((1397 / 32 : ℚ) : ℝ) ≤ ((260583 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2794
  constructor
  · exact (show ((130289 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((190735730639 / 1152921504606846976 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1397 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((3051771690227 / 18446744073709551616 : ℚ) : ℝ) ≤ ((260583 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2795 : ((751114588895 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((2795 / 64 : ℚ) : ℝ) ∧
    heightZ ((2795 / 64 : ℚ) : ℝ) ≤ ((3004458355583 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((751114588895 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((2795 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2657 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2795 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2657 / 192 : ℚ) : ℝ) ≤ ((3004458355583 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2795 : ((252561 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2795 / 64 : ℚ) : ℝ) ∧
    logKernel ((2795 / 64 : ℚ) : ℝ) ≤ ((126283 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2795
  constructor
  · exact (show ((252561 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((751114588895 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2795 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((3004458355583 / 18446744073709551616 : ℚ) : ℝ) ≤ ((126283 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2796 : ((2957878546199 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((699 / 16 : ℚ) : ℝ) ∧
    heightZ ((699 / 16 : ℚ) : ℝ) ≤ ((1478939273101 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((2957878546199 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((699 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-665 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((699 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-665 / 48 : ℚ) : ℝ) ≤ ((1478939273101 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2796 : ((244791 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((699 / 16 : ℚ) : ℝ) ∧
    logKernel ((699 / 16 : ℚ) : ℝ) ≤ ((61199 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2796
  constructor
  · exact (show ((244791 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((2957878546199 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((699 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1478939273101 / 9223372036854775808 : ℚ) : ℝ) ≤ ((61199 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2797 : ((728005222457 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((2797 / 64 : ℚ) : ℝ) ∧
    heightZ ((2797 / 64 : ℚ) : ℝ) ≤ ((2912020889831 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((728005222457 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((2797 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2663 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2797 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2663 / 192 : ℚ) : ℝ) ≤ ((2912020889831 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2797 : ((237259 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2797 / 64 : ℚ) : ℝ) ∧
    logKernel ((2797 / 64 : ℚ) : ℝ) ≤ ((14829 / 4503599627370496 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2797
  constructor
  · exact (show ((237259 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((728005222457 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2797 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((2912020889831 / 18446744073709551616 : ℚ) : ℝ) ≤ ((14829 / 4503599627370496 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2798 : ((2866874190521 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1399 / 32 : ℚ) : ℝ) ∧
    heightZ ((1399 / 32 : ℚ) : ℝ) ≤ ((716718547631 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((2866874190521 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1399 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1333 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1399 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1333 / 96 : ℚ) : ℝ) ≤ ((716718547631 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2798 : ((229959 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1399 / 32 : ℚ) : ℝ) ∧
    logKernel ((1399 / 32 : ℚ) : ℝ) ≤ ((57491 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2798
  constructor
  · exact (show ((229959 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((2866874190521 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1399 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((716718547631 / 4611686018427387904 : ℚ) : ℝ) ≤ ((57491 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2799 : ((2822427425911 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2799 / 64 : ℚ) : ℝ) ∧
    heightZ ((2799 / 64 : ℚ) : ℝ) ≤ ((1411213712957 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((2822427425911 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2799 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2669 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2799 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2669 / 192 : ℚ) : ℝ) ≤ ((1411213712957 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2799 : ((55721 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((2799 / 64 : ℚ) : ℝ) ∧
    logKernel ((2799 / 64 : ℚ) : ℝ) ≤ ((222889 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2799
  constructor
  · exact (show ((55721 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((2822427425911 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2799 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1411213712957 / 9223372036854775808 : ℚ) : ℝ) ≤ ((222889 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2800 : ((2778669744515 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((175 / 4 : ℚ) : ℝ) ∧
    heightZ ((175 / 4 : ℚ) : ℝ) ≤ ((1389334872259 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((2778669744515 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((175 / 4 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-167 / 12 : ℚ) : ℝ) ∧
      Real.exp (-((175 / 4 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-167 / 12 : ℚ) : ℝ) ≤ ((1389334872259 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2800 : ((216027 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((175 / 4 : ℚ) : ℝ) ∧
    logKernel ((175 / 4 : ℚ) : ℝ) ≤ ((6751 / 2251799813685248 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2800
  constructor
  · exact (show ((216027 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((2778669744515 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((175 / 4 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1389334872259 / 9223372036854775808 : ℚ) : ℝ) ≤ ((6751 / 2251799813685248 : ℚ) : ℝ) by norm_num [zKernel])

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

theorem log_height_bounds_928 : ((135746401659929673 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((1385 / 32 : ℚ) : ℝ) ∧
    Real.log ((1385 / 32 : ℚ) : ℝ) ≤ ((271492803319859349 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((135746401659929673 / 36028797018963968 : ℚ) : ℝ) ≤ ((1385 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1385 / 32 : ℚ) : ℝ) ≤ Real.exp ((271492803319859349 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_928 : heightPower (928 : Fin 988) ≤ ((2098162962692677 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_928
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_928 : heightFactor (928 : Fin 988) ≤ ((36955701 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_928
  obtain ⟨hpl, hph⟩ := kernel_bounds_2769
  obtain ⟨hcl, hch⟩ := kernel_bounds_2770
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2770
  have h : (((1918225 / 512 : ℚ) : ℝ) * (logKernel ((2769 / 64 : ℚ) : ℝ) - logKernel ((1385 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1385 / 32 : ℚ) : ℝ) + Real.log ((1385 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((36955701 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_929 : ((271518812197253407 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2771 / 64 : ℚ) : ℝ) ∧
    Real.log ((2771 / 64 : ℚ) : ℝ) ≤ ((135759406098626705 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((271518812197253407 / 72057594037927936 : ℚ) : ℝ) ≤ ((2771 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2771 / 64 : ℚ) : ℝ) ≤ Real.exp ((135759406098626705 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_929 : heightPower (929 : Fin 988) ≤ ((4200825569073779 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_929
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_929 : heightFactor (929 : Fin 988) ≤ ((4504713 / 35184372088832 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_929
  obtain ⟨hpl, hph⟩ := kernel_bounds_2770
  obtain ⟨hcl, hch⟩ := kernel_bounds_2771
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2771
  have h : (((7678441 / 2048 : ℚ) : ℝ) * (logKernel ((1385 / 32 : ℚ) : ℝ) - logKernel ((2771 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2771 / 64 : ℚ) : ℝ) + Real.log ((2771 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((4504713 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_930 : ((271544811690242647 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((693 / 16 : ℚ) : ℝ) ∧
    Real.log ((693 / 16 : ℚ) : ℝ) ≤ ((135772405845121325 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((271544811690242647 / 72057594037927936 : ℚ) : ℝ) ≤ ((693 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((693 / 16 : ℚ) : ℝ) ≤ Real.exp ((135772405845121325 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_930 : heightPower (930 : Fin 988) ≤ ((1051331294026093 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_930
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_930 : heightFactor (930 : Fin 988) ≤ ((8785635 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_930
  obtain ⟨hpl, hph⟩ := kernel_bounds_2771
  obtain ⟨hcl, hch⟩ := kernel_bounds_2772
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2772
  have h : (((480249 / 128 : ℚ) : ℝ) * (logKernel ((2771 / 64 : ℚ) : ℝ) - logKernel ((693 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((693 / 16 : ℚ) : ℝ) + Real.log ((693 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((8785635 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_931 : ((271570801805596701 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2773 / 64 : ℚ) : ℝ) ∧
    Real.log ((2773 / 64 : ℚ) : ℝ) ≤ ((8486587556424897 / 2251799813685248 : ℚ) : ℝ) := by
  have hl : Real.exp ((271570801805596701 / 72057594037927936 : ℚ) : ℝ) ≤ ((2773 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2773 / 64 : ℚ) : ℝ) ≤ Real.exp ((8486587556424897 / 2251799813685248 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_931 : heightPower (931 : Fin 988) ≤ ((2104912373251789 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_931
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_931 : heightFactor (931 : Fin 988) ≤ ((17134821 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_931
  obtain ⟨hpl, hph⟩ := kernel_bounds_2772
  obtain ⟨hcl, hch⟩ := kernel_bounds_2773
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2773
  have h : (((7689529 / 2048 : ℚ) : ℝ) * (logKernel ((693 / 16 : ℚ) : ℝ) - logKernel ((2773 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2773 / 64 : ℚ) : ℝ) + Real.log ((2773 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((17134821 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_932 : ((271596782550077881 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1387 / 32 : ℚ) : ℝ) ∧
    Real.log ((1387 / 32 : ℚ) : ℝ) ≤ ((67899195637519471 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((271596782550077881 / 72057594037927936 : ℚ) : ℝ) ≤ ((1387 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1387 / 32 : ℚ) : ℝ) ≤ Real.exp ((67899195637519471 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_932 : heightPower (932 : Fin 988) ≤ ((4214324280297811 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_932
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_932 : heightFactor (932 : Fin 988) ≤ ((4177307 / 35184372088832 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_932
  obtain ⟨hpl, hph⟩ := kernel_bounds_2773
  obtain ⟨hcl, hch⟩ := kernel_bounds_2774
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2774
  have h : (((1923769 / 512 : ℚ) : ℝ) * (logKernel ((2773 / 64 : ℚ) : ℝ) - logKernel ((1387 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1387 / 32 : ℚ) : ℝ) + Real.log ((1387 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((4177307 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_933 : ((135811376965220593 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2775 / 64 : ℚ) : ℝ) ∧
    Real.log ((2775 / 64 : ℚ) : ℝ) ≤ ((271622753930441189 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((135811376965220593 / 36028797018963968 : ℚ) : ℝ) ≤ ((2775 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2775 / 64 : ℚ) : ℝ) ≤ Real.exp ((271622753930441189 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_933 : heightPower (933 : Fin 988) ≤ ((4218823777513459 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_933
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_933 : heightFactor (933 : Fin 988) ≤ ((16294221 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_933
  obtain ⟨hpl, hph⟩ := kernel_bounds_2774
  obtain ⟨hcl, hch⟩ := kernel_bounds_2775
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2775
  have h : (((7700625 / 2048 : ℚ) : ℝ) * (logKernel ((1387 / 32 : ℚ) : ℝ) - logKernel ((2775 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2775 / 64 : ℚ) : ℝ) + Real.log ((2775 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((16294221 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_934 : ((271648715953434315 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((347 / 8 : ℚ) : ℝ) ∧
    Real.log ((347 / 8 : ℚ) : ℝ) ≤ ((135824357976717159 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((271648715953434315 / 72057594037927936 : ℚ) : ℝ) ≤ ((347 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((347 / 8 : ℚ) : ℝ) ≤ Real.exp ((135824357976717159 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_934 : heightPower (934 : Fin 988) ≤ ((263957702386055 / 17592186044416 : ℚ) : ℝ) := by
  have hh := log_height_bounds_934
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_934 : heightFactor (934 : Fin 988) ≤ ((31779075 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_934
  obtain ⟨hpl, hph⟩ := kernel_bounds_2775
  obtain ⟨hcl, hch⟩ := kernel_bounds_2776
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2776
  have h : (((120409 / 32 : ℚ) : ℝ) * (logKernel ((2775 / 64 : ℚ) : ℝ) - logKernel ((347 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((347 / 8 : ℚ) : ℝ) + Real.log ((347 / 8 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((31779075 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_935 : ((135837334312898837 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2777 / 64 : ℚ) : ℝ) ∧
    Real.log ((2777 / 64 : ℚ) : ℝ) ≤ ((271674668625797677 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((135837334312898837 / 36028797018963968 : ℚ) : ℝ) ≤ ((2777 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2777 / 64 : ℚ) : ℝ) ≤ Real.exp ((271674668625797677 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_935 : heightPower (935 : Fin 988) ≤ ((1056955665578601 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_935
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_935 : heightFactor (935 : Fin 988) ≤ ((30989839 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_935
  obtain ⟨hpl, hph⟩ := kernel_bounds_2776
  obtain ⟨hcl, hch⟩ := kernel_bounds_2777
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2777
  have h : (((7711729 / 2048 : ℚ) : ℝ) * (logKernel ((347 / 8 : ℚ) : ℝ) - logKernel ((2777 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2777 / 64 : ℚ) : ℝ) + Real.log ((2777 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((30989839 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_936 : ((135850305977132195 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((1389 / 32 : ℚ) : ℝ) ∧
    Real.log ((1389 / 32 : ℚ) : ℝ) ≤ ((271700611954264393 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((135850305977132195 / 36028797018963968 : ℚ) : ℝ) ≤ ((1389 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1389 / 32 : ℚ) : ℝ) ≤ Real.exp ((271700611954264393 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_936 : heightPower (936 : Fin 988) ≤ ((4232322049952331 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_936
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_936 : heightFactor (936 : Fin 988) ≤ ((7555059 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_936
  obtain ⟨hpl, hph⟩ := kernel_bounds_2777
  obtain ⟨hcl, hch⟩ := kernel_bounds_2778
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2778
  have h : (((1929321 / 512 : ℚ) : ℝ) * (logKernel ((2777 / 64 : ℚ) : ℝ) - logKernel ((1389 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1389 / 32 : ℚ) : ℝ) + Real.log ((1389 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((7555059 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_937 : ((135863272972780161 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2779 / 64 : ℚ) : ℝ) ∧
    Real.log ((2779 / 64 : ℚ) : ℝ) ≤ ((271726545945560325 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((135863272972780161 / 36028797018963968 : ℚ) : ℝ) ≤ ((2779 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2779 / 64 : ℚ) : ℝ) ≤ Real.exp ((271726545945560325 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_937 : heightPower (937 : Fin 988) ≤ ((4236821401116935 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_937
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_937 : heightFactor (937 : Fin 988) ≤ ((29469777 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_937
  obtain ⟨hpl, hph⟩ := kernel_bounds_2778
  obtain ⟨hcl, hch⟩ := kernel_bounds_2779
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2779
  have h : (((7722841 / 2048 : ℚ) : ℝ) * (logKernel ((1389 / 32 : ℚ) : ℝ) - logKernel ((2779 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2779 / 64 : ℚ) : ℝ) + Real.log ((2779 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((29469777 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_938 : ((135876235303202033 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((695 / 16 : ℚ) : ℝ) ∧
    Real.log ((695 / 16 : ℚ) : ℝ) ≤ ((271752470606404069 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((135876235303202033 / 36028797018963968 : ℚ) : ℝ) ≤ ((695 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((695 / 16 : ℚ) : ℝ) ≤ Real.exp ((271752470606404069 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_938 : heightPower (938 : Fin 988) ≤ ((4241320715834459 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_938
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_938 : heightFactor (938 : Fin 988) ≤ ((14368993 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_938
  obtain ⟨hpl, hph⟩ := kernel_bounds_2779
  obtain ⟨hcl, hch⟩ := kernel_bounds_2780
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2780
  have h : (((483025 / 128 : ℚ) : ℝ) * (logKernel ((2779 / 64 : ℚ) : ℝ) - logKernel ((695 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((695 / 16 : ℚ) : ℝ) + Real.log ((695 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((14368993 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_939 : ((135889192971753485 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2781 / 64 : ℚ) : ℝ) ∧
    Real.log ((2781 / 64 : ℚ) : ℝ) ≤ ((271778385943506973 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((135889192971753485 / 36028797018963968 : ℚ) : ℝ) ≤ ((2781 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2781 / 64 : ℚ) : ℝ) ≤ Real.exp ((271778385943506973 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_939 : heightPower (939 : Fin 988) ≤ ((2122909997065561 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_939
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_939 : heightFactor (939 : Fin 988) ≤ ((28024399 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_939
  obtain ⟨hpl, hph⟩ := kernel_bounds_2780
  obtain ⟨hcl, hch⟩ := kernel_bounds_2781
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2781
  have h : (((7733961 / 2048 : ℚ) : ℝ) * (logKernel ((695 / 16 : ℚ) : ℝ) - logKernel ((2781 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2781 / 64 : ℚ) : ℝ) + Real.log ((2781 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((28024399 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_940 : ((135902145981786573 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((1391 / 32 : ℚ) : ℝ) ∧
    Real.log ((1391 / 32 : ℚ) : ℝ) ≤ ((271804291963573149 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((135902145981786573 / 36028797018963968 : ℚ) : ℝ) ≤ ((1391 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1391 / 32 : ℚ) : ℝ) ≤ Real.exp ((271804291963573149 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_940 : heightPower (940 : Fin 988) ≤ ((4250319236033109 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_940
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_940 : heightFactor (940 : Fin 988) ≤ ((27328563 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_940
  obtain ⟨hpl, hph⟩ := kernel_bounds_2781
  obtain ⟨hcl, hch⟩ := kernel_bounds_2782
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2782
  have h : (((1934881 / 512 : ℚ) : ℝ) * (logKernel ((2781 / 64 : ℚ) : ℝ) - logKernel ((1391 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1391 / 32 : ℚ) : ℝ) + Real.log ((1391 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((27328563 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_941 : ((67957547168324869 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((2783 / 64 : ℚ) : ℝ) ∧
    Real.log ((2783 / 64 : ℚ) : ℝ) ≤ ((271830188673299479 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((67957547168324869 / 18014398509481984 : ℚ) : ℝ) ≤ ((2783 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2783 / 64 : ℚ) : ℝ) ≤ Real.exp ((271830188673299479 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_941 : heightPower (941 : Fin 988) ≤ ((2127409220783291 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_941
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_941 : heightFactor (941 : Fin 988) ≤ ((26650037 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_941
  obtain ⟨hpl, hph⟩ := kernel_bounds_2782
  obtain ⟨hcl, hch⟩ := kernel_bounds_2783
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2783
  have h : (((7745089 / 2048 : ℚ) : ℝ) * (logKernel ((1391 / 32 : ℚ) : ℝ) - logKernel ((2783 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2783 / 64 : ℚ) : ℝ) + Real.log ((2783 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((26650037 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_942 : ((135928038039687811 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((87 / 2 : ℚ) : ℝ) ∧
    Real.log ((87 / 2 : ℚ) : ℝ) ≤ ((271856076079375625 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((135928038039687811 / 36028797018963968 : ℚ) : ℝ) ≤ ((87 / 2 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((87 / 2 : ℚ) : ℝ) ≤ Real.exp ((271856076079375625 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_942 : heightPower (942 : Fin 988) ≤ ((4259317610757671 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_942
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_942 : heightFactor (942 : Fin 988) ≤ ((12994195 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_942
  obtain ⟨hpl, hph⟩ := kernel_bounds_2783
  obtain ⟨hcl, hch⟩ := kernel_bounds_2784
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2784
  have h : (((7569 / 2 : ℚ) : ℝ) * (logKernel ((2783 / 64 : ℚ) : ℝ) - logKernel ((87 / 2 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((87 / 2 : ℚ) : ℝ) + Real.log ((87 / 2 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((12994195 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_943 : ((271881954188484043 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2785 / 64 : ℚ) : ℝ) ∧
    Real.log ((2785 / 64 : ℚ) : ℝ) ≤ ((135940977094242023 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((271881954188484043 / 72057594037927936 : ℚ) : ℝ) ≤ ((2785 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2785 / 64 : ℚ) : ℝ) ≤ Real.exp ((135940977094242023 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_943 : heightPower (943 : Fin 988) ≤ ((4263816743632479 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_943
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_943 : heightFactor (943 : Fin 988) ≤ ((25343203 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_943
  obtain ⟨hpl, hph⟩ := kernel_bounds_2784
  obtain ⟨hcl, hch⟩ := kernel_bounds_2785
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2785
  have h : (((7756225 / 2048 : ℚ) : ℝ) * (logKernel ((87 / 2 : ℚ) : ℝ) - logKernel ((2785 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2785 / 64 : ℚ) : ℝ) + Real.log ((2785 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((25343203 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_944 : ((271907823007299997 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1393 / 32 : ℚ) : ℝ) ∧
    Real.log ((1393 / 32 : ℚ) : ℝ) ≤ ((8497119468978125 / 2251799813685248 : ℚ) : ℝ) := by
  have hl : Real.exp ((271907823007299997 / 72057594037927936 : ℚ) : ℝ) ≤ ((1393 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1393 / 32 : ℚ) : ℝ) ≤ Real.exp ((8497119468978125 / 2251799813685248 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_944 : heightPower (944 : Fin 988) ≤ ((4268315840217083 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_944
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_944 : heightFactor (944 : Fin 988) ≤ ((24714067 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_944
  obtain ⟨hpl, hph⟩ := kernel_bounds_2785
  obtain ⟨hcl, hch⟩ := kernel_bounds_2786
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2786
  have h : (((1940449 / 512 : ℚ) : ℝ) * (logKernel ((2785 / 64 : ℚ) : ℝ) - logKernel ((1393 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1393 / 32 : ℚ) : ℝ) + Real.log ((1393 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((24714067 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_945 : ((135966841271245779 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2787 / 64 : ℚ) : ℝ) ∧
    Real.log ((2787 / 64 : ℚ) : ℝ) ≤ ((271933682542491561 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((135966841271245779 / 36028797018963968 : ℚ) : ℝ) ≤ ((2787 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2787 / 64 : ℚ) : ℝ) ≤ Real.exp ((271933682542491561 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_945 : heightPower (945 : Fin 988) ≤ ((4272814900537529 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_945
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_945 : heightFactor (945 : Fin 988) ≤ ((24100581 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_945
  obtain ⟨hpl, hph⟩ := kernel_bounds_2786
  obtain ⟨hcl, hch⟩ := kernel_bounds_2787
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2787
  have h : (((7767369 / 2048 : ℚ) : ℝ) * (logKernel ((1393 / 32 : ℚ) : ℝ) - logKernel ((2787 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2787 / 64 : ℚ) : ℝ) + Real.log ((2787 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((24100581 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_946 : ((271959532800719623 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((697 / 16 : ℚ) : ℝ) ∧
    Real.log ((697 / 16 : ℚ) : ℝ) ≤ ((135979766400359813 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((271959532800719623 / 72057594037927936 : ℚ) : ℝ) ≤ ((697 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((697 / 16 : ℚ) : ℝ) ≤ Real.exp ((135979766400359813 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_946 : heightPower (946 : Fin 988) ≤ ((4277313924619837 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_946
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_946 : heightFactor (946 : Fin 988) ≤ ((11751179 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_946
  obtain ⟨hpl, hph⟩ := kernel_bounds_2787
  obtain ⟨hcl, hch⟩ := kernel_bounds_2788
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2788
  have h : (((485809 / 128 : ℚ) : ℝ) * (logKernel ((2787 / 64 : ℚ) : ℝ) - logKernel ((697 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((697 / 16 : ℚ) : ℝ) + Real.log ((697 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((11751179 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_947 : ((135992686894318961 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2789 / 64 : ℚ) : ℝ) ∧
    Real.log ((2789 / 64 : ℚ) : ℝ) ≤ ((271985373788637925 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((135992686894318961 / 36028797018963968 : ℚ) : ℝ) ≤ ((2789 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2789 / 64 : ℚ) : ℝ) ≤ Real.exp ((271985373788637925 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_947 : heightPower (947 : Fin 988) ≤ ((1070453228122499 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_947
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_947 : heightFactor (947 : Fin 988) ≤ ((11459509 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_947
  obtain ⟨hpl, hph⟩ := kernel_bounds_2788
  obtain ⟨hcl, hch⟩ := kernel_bounds_2789
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2789
  have h : (((7778521 / 2048 : ℚ) : ℝ) * (logKernel ((697 / 16 : ℚ) : ℝ) - logKernel ((2789 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2789 / 64 : ℚ) : ℝ) + Real.log ((2789 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((11459509 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_948 : ((136005602756446515 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((1395 / 32 : ℚ) : ℝ) ∧
    Real.log ((1395 / 32 : ℚ) : ℝ) ≤ ((272011205512893033 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((136005602756446515 / 36028797018963968 : ℚ) : ℝ) ≤ ((1395 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1395 / 32 : ℚ) : ℝ) ≤ Real.exp ((272011205512893033 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_948 : heightPower (948 : Fin 988) ≤ ((1071577966043493 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_948
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_948 : heightFactor (948 : Fin 988) ≤ ((22350191 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_948
  obtain ⟨hpl, hph⟩ := kernel_bounds_2789
  obtain ⟨hcl, hch⟩ := kernel_bounds_2790
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2790
  have h : (((1946025 / 512 : ℚ) : ℝ) * (logKernel ((2789 / 64 : ℚ) : ℝ) - logKernel ((1395 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1395 / 32 : ℚ) : ℝ) + Real.log ((1395 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((22350191 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_949 : ((34004628497515547 / 9007199254740992 : ℚ) : ℝ) ≤ Real.log ((2791 / 64 : ℚ) : ℝ) ∧
    Real.log ((2791 / 64 : ℚ) : ℝ) ≤ ((272037027980124379 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((34004628497515547 / 9007199254740992 : ℚ) : ℝ) ≤ ((2791 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2791 / 64 : ℚ) : ℝ) ≤ Real.exp ((272037027980124379 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_949 : heightPower (949 : Fin 988) ≤ ((2145405389848849 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_949
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_949 : heightFactor (949 : Fin 988) ≤ ((21795515 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_949
  obtain ⟨hpl, hph⟩ := kernel_bounds_2790
  obtain ⟨hcl, hch⟩ := kernel_bounds_2791
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2791
  have h : (((7789681 / 2048 : ℚ) : ℝ) * (logKernel ((1395 / 32 : ℚ) : ℝ) - logKernel ((2791 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2791 / 64 : ℚ) : ℝ) + Real.log ((2791 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((21795515 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_950 : ((272062841196964253 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((349 / 8 : ℚ) : ℝ) ∧
    Real.log ((349 / 8 : ℚ) : ℝ) ≤ ((8501963787405133 / 2251799813685248 : ℚ) : ℝ) := by
  have hl : Real.exp ((272062841196964253 / 72057594037927936 : ℚ) : ℝ) ≤ ((349 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((349 / 8 : ℚ) : ℝ) ≤ Real.exp ((8501963787405133 / 2251799813685248 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_950 : heightPower (950 : Fin 988) ≤ ((4295309659087083 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_950
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_950 : heightFactor (950 : Fin 988) ≤ ((10627319 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_950
  obtain ⟨hpl, hph⟩ := kernel_bounds_2791
  obtain ⟨hcl, hch⟩ := kernel_bounds_2792
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2792
  have h : (((121801 / 32 : ℚ) : ℝ) * (logKernel ((2791 / 64 : ℚ) : ℝ) - logKernel ((349 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((349 / 8 : ℚ) : ℝ) + Real.log ((349 / 8 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((10627319 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_951 : ((272088645170037831 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2793 / 64 : ℚ) : ℝ) ∧
    Real.log ((2793 / 64 : ℚ) : ℝ) ≤ ((136044322585018917 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((272088645170037831 / 72057594037927936 : ℚ) : ℝ) ≤ ((2793 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2793 / 64 : ℚ) : ℝ) ≤ Real.exp ((136044322585018917 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_951 : heightPower (951 : Fin 988) ≤ ((2149904251184003 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_951
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_951 : heightFactor (951 : Fin 988) ≤ ((20727219 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_951
  obtain ⟨hpl, hph⟩ := kernel_bounds_2792
  obtain ⟨hcl, hch⟩ := kernel_bounds_2793
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2793
  have h : (((7800849 / 2048 : ℚ) : ℝ) * (logKernel ((349 / 8 : ℚ) : ℝ) - logKernel ((2793 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2793 / 64 : ℚ) : ℝ) + Real.log ((2793 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((20727219 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_952 : ((272114439905963163 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1397 / 32 : ℚ) : ℝ) ∧
    Real.log ((1397 / 32 : ℚ) : ℝ) ≤ ((136057219952981583 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((272114439905963163 / 72057594037927936 : ℚ) : ℝ) ≤ ((1397 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1397 / 32 : ℚ) : ℝ) ≤ Real.exp ((136057219952981583 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_952 : heightPower (952 : Fin 988) ≤ ((2152153654783159 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_952
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_952 : heightFactor (952 : Fin 988) ≤ ((20212921 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_952
  obtain ⟨hpl, hph⟩ := kernel_bounds_2793
  obtain ⟨hcl, hch⟩ := kernel_bounds_2794
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2794
  have h : (((1951609 / 512 : ℚ) : ℝ) * (logKernel ((2793 / 64 : ℚ) : ℝ) - logKernel ((1397 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1397 / 32 : ℚ) : ℝ) + Real.log ((1397 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((20212921 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_953 : ((136070112705675599 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2795 / 64 : ℚ) : ℝ) ∧
    Real.log ((2795 / 64 : ℚ) : ℝ) ≤ ((272140225411351201 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((136070112705675599 / 36028797018963968 : ℚ) : ℝ) ≤ ((2795 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2795 / 64 : ℚ) : ℝ) ≤ Real.exp ((272140225411351201 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_953 : heightPower (953 : Fin 988) ≤ ((1077201520176961 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_953
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_953 : heightFactor (953 : Fin 988) ≤ ((4927855 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_953
  obtain ⟨hpl, hph⟩ := kernel_bounds_2794
  obtain ⟨hcl, hch⟩ := kernel_bounds_2795
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2795
  have h : (((7812025 / 2048 : ℚ) : ℝ) * (logKernel ((1397 / 32 : ℚ) : ℝ) - logKernel ((2795 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2795 / 64 : ℚ) : ℝ) + Real.log ((2795 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((4927855 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_954 : ((272166001692805791 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((699 / 16 : ℚ) : ℝ) ∧
    Real.log ((699 / 16 : ℚ) : ℝ) ≤ ((136083000846402897 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((272166001692805791 / 72057594037927936 : ℚ) : ℝ) ≤ ((699 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((699 / 16 : ℚ) : ℝ) ≤ Real.exp ((136083000846402897 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_954 : heightPower (954 : Fin 988) ≤ ((1078326203954595 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_954
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_954 : heightFactor (954 : Fin 988) ≤ ((19222395 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_954
  obtain ⟨hpl, hph⟩ := kernel_bounds_2795
  obtain ⟨hcl, hch⟩ := kernel_bounds_2796
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2796
  have h : (((488601 / 128 : ℚ) : ℝ) * (logKernel ((2795 / 64 : ℚ) : ℝ) - logKernel ((699 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((699 / 16 : ℚ) : ℝ) + Real.log ((699 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((19222395 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_955 : ((272191768756923711 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2797 / 64 : ℚ) : ℝ) ∧
    Real.log ((2797 / 64 : ℚ) : ℝ) ≤ ((136095884378461857 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((272191768756923711 / 72057594037927936 : ℚ) : ℝ) ≤ ((2797 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2797 / 64 : ℚ) : ℝ) ≤ Real.exp ((136095884378461857 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_955 : heightPower (955 : Fin 988) ≤ ((4317803514923695 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_955
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_955 : heightFactor (955 : Fin 988) ≤ ((9372769 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_955
  obtain ⟨hpl, hph⟩ := kernel_bounds_2796
  obtain ⟨hcl, hch⟩ := kernel_bounds_2797
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2797
  have h : (((7823209 / 2048 : ℚ) : ℝ) * (logKernel ((699 / 16 : ℚ) : ℝ) - logKernel ((2797 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2797 / 64 : ℚ) : ℝ) + Real.log ((2797 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((9372769 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_956 : ((272217526610294655 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1399 / 32 : ℚ) : ℝ) ∧
    Real.log ((1399 / 32 : ℚ) : ℝ) ≤ ((136108763305147329 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((272217526610294655 / 72057594037927936 : ℚ) : ℝ) ≤ ((1399 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1399 / 32 : ℚ) : ℝ) ≤ Real.exp ((136108763305147329 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_956 : heightPower (956 : Fin 988) ≤ ((4322302178049529 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_956
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_956 : heightFactor (956 : Fin 988) ≤ ((9140273 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_956
  obtain ⟨hpl, hph⟩ := kernel_bounds_2797
  obtain ⟨hcl, hch⟩ := kernel_bounds_2798
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2798
  have h : (((1957201 / 512 : ℚ) : ℝ) * (logKernel ((2797 / 64 : ℚ) : ℝ) - logKernel ((1399 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1399 / 32 : ℚ) : ℝ) + Real.log ((1399 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((9140273 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_957 : ((136121637629750627 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2799 / 64 : ℚ) : ℝ) ∧
    Real.log ((2799 / 64 : ℚ) : ℝ) ≤ ((272243275259501257 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((136121637629750627 / 36028797018963968 : ℚ) : ℝ) ≤ ((2799 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2799 / 64 : ℚ) : ℝ) ≤ Real.exp ((272243275259501257 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_957 : heightPower (957 : Fin 988) ≤ ((1081700201305399 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_957
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_957 : heightFactor (957 : Fin 988) ≤ ((17827123 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_957
  obtain ⟨hpl, hph⟩ := kernel_bounds_2798
  obtain ⟨hcl, hch⟩ := kernel_bounds_2799
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2799
  have h : (((7834401 / 2048 : ℚ) : ℝ) * (logKernel ((1399 / 32 : ℚ) : ℝ) - logKernel ((2799 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2799 / 64 : ℚ) : ℝ) + Real.log ((2799 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((17827123 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_958 : ((136134507355559543 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((175 / 4 : ℚ) : ℝ) ∧
    Real.log ((175 / 4 : ℚ) : ℝ) ≤ ((272269014711119089 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((136134507355559543 / 36028797018963968 : ℚ) : ℝ) ≤ ((175 / 4 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((175 / 4 : ℚ) : ℝ) ≤ Real.exp ((272269014711119089 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_958 : heightPower (958 : Fin 988) ≤ ((2165649698232791 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_958
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_958 : heightFactor (958 : Fin 988) ≤ ((8692491 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_958
  obtain ⟨hpl, hph⟩ := kernel_bounds_2799
  obtain ⟨hcl, hch⟩ := kernel_bounds_2800
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2800
  have h : (((30625 / 8 : ℚ) : ℝ) * (logKernel ((2799 / 64 : ℚ) : ℝ) - logKernel ((175 / 4 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((175 / 4 : ℚ) : ℝ) + Real.log ((175 / 4 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((8692491 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_959 : ((68073686242929171 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((2801 / 64 : ℚ) : ℝ) ∧
    Real.log ((2801 / 64 : ℚ) : ℝ) ≤ ((272294744971716687 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((68073686242929171 / 18014398509481984 : ℚ) : ℝ) ≤ ((2801 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2801 / 64 : ℚ) : ℝ) ≤ Real.exp ((272294744971716687 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_959 : heightPower (959 : Fin 988) ≤ ((2167898975903573 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_959
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_959 : heightFactor (959 : Fin 988) ≤ ((8476921 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_959
  obtain ⟨hpl, hph⟩ := kernel_bounds_2800
  obtain ⟨hcl, hch⟩ := kernel_bounds_2801
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2801
  have h : (((7845601 / 2048 : ℚ) : ℝ) * (logKernel ((175 / 4 : ℚ) : ℝ) - logKernel ((2801 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2801 / 64 : ℚ) : ℝ) + Real.log ((2801 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((8476921 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

end LegendreK6.M2Pilot.Enclosures.Height029
