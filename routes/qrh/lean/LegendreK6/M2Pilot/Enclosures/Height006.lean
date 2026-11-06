import LegendreK6.M2PilotDefinitions
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp

/-! Generated proposals: every bound is checked by Lean, not by trusting Arb. -/
namespace LegendreK6.M2Pilot.Enclosures.Height006
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem height_z_bounds_2033 : ((445230455228281785 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2033 / 64 : ℚ) : ℝ) ∧
    heightZ ((2033 / 64 : ℚ) : ℝ) ≤ ((111307613807070447 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((445230455228281785 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2033 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-371 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2033 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-371 / 192 : ℚ) : ℝ) ≤ ((111307613807070447 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2033 : ((3590568187324851 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2033 / 64 : ℚ) : ℝ) ∧
    logKernel ((2033 / 64 : ℚ) : ℝ) ≤ ((448821023415607 / 9007199254740992 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2033
  constructor
  · exact (show ((3590568187324851 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((445230455228281785 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2033 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((111307613807070447 / 4611686018427387904 : ℚ) : ℝ) ≤ ((448821023415607 / 9007199254740992 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2034 : ((219163898409269713 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((1017 / 32 : ℚ) : ℝ) ∧
    heightZ ((1017 / 32 : ℚ) : ℝ) ≤ ((438327796818539429 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((219163898409269713 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((1017 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-187 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1017 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-187 / 96 : ℚ) : ℝ) ≤ ((438327796818539429 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2034 : ((3534901587246283 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1017 / 32 : ℚ) : ℝ) ∧
    logKernel ((1017 / 32 : ℚ) : ℝ) ≤ ((220931349202893 / 4503599627370496 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2034
  constructor
  · exact (show ((3534901587246283 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((219163898409269713 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1017 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((438327796818539429 / 18446744073709551616 : ℚ) : ℝ) ≤ ((220931349202893 / 4503599627370496 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2035 : ((431532154208282655 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2035 / 64 : ℚ) : ℝ) ∧
    heightZ ((2035 / 64 : ℚ) : ℝ) ≤ ((215766077104141329 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((431532154208282655 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2035 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-377 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2035 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-377 / 192 : ℚ) : ℝ) ≤ ((215766077104141329 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2035 : ((3480098017808729 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2035 / 64 : ℚ) : ℝ) ∧
    logKernel ((2035 / 64 : ℚ) : ℝ) ≤ ((1740049008904367 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2035
  constructor
  · exact (show ((3480098017808729 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((431532154208282655 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2035 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((215766077104141329 / 9223372036854775808 : ℚ) : ℝ) ≤ ((1740049008904367 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2036 : ((424841868271322731 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((509 / 16 : ℚ) : ℝ) ∧
    heightZ ((509 / 16 : ℚ) : ℝ) ≤ ((212420934135661367 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((424841868271322731 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((509 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-95 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((509 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-95 / 48 : ℚ) : ℝ) ≤ ((212420934135661367 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2036 : ((1713072049481139 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((509 / 16 : ℚ) : ℝ) ∧
    logKernel ((509 / 16 : ℚ) : ℝ) ≤ ((3426144098962283 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2036
  constructor
  · exact (show ((1713072049481139 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((424841868271322731 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((509 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((212420934135661367 / 9223372036854775808 : ℚ) : ℝ) ≤ ((3426144098962283 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2037 : ((418255305603838295 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2037 / 64 : ℚ) : ℝ) ∧
    heightZ ((2037 / 64 : ℚ) : ℝ) ≤ ((209127652801919149 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((418255305603838295 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2037 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-383 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2037 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-383 / 192 : ℚ) : ℝ) ≤ ((209127652801919149 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2037 : ((843256664523867 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((2037 / 64 : ℚ) : ℝ) ∧
    logKernel ((2037 / 64 : ℚ) : ℝ) ≤ ((3373026658095473 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2037
  constructor
  · exact (show ((843256664523867 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((418255305603838295 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2037 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((209127652801919149 / 9223372036854775808 : ℚ) : ℝ) ≤ ((3373026658095473 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2038 : ((205885429062793515 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((1019 / 32 : ℚ) : ℝ) ∧
    heightZ ((1019 / 32 : ℚ) : ℝ) ≤ ((411770858125587033 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((205885429062793515 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((1019 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-193 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1019 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-193 / 96 : ℚ) : ℝ) ≤ ((411770858125587033 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2038 : ((207545795426203 / 4503599627370496 : ℚ) : ℝ) ≤ logKernel ((1019 / 32 : ℚ) : ℝ) ∧
    logKernel ((1019 / 32 : ℚ) : ℝ) ≤ ((3320732726819253 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2038
  constructor
  · exact (show ((207545795426203 / 4503599627370496 : ℚ) : ℝ) ≤ zKernel ((205885429062793515 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1019 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((411770858125587033 / 18446744073709551616 : ℚ) : ℝ) ≤ ((3320732726819253 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2039 : ((405386942687299953 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2039 / 64 : ℚ) : ℝ) ∧
    heightZ ((2039 / 64 : ℚ) : ℝ) ≤ ((101346735671824989 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((405386942687299953 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2039 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-389 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2039 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-389 / 192 : ℚ) : ℝ) ≤ ((101346735671824989 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2039 : ((817312384450201 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((2039 / 64 : ℚ) : ℝ) ∧
    logKernel ((2039 / 64 : ℚ) : ℝ) ≤ ((3269249537800809 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2039
  constructor
  · exact (show ((817312384450201 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((405386942687299953 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2039 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((101346735671824989 / 4611686018427387904 : ℚ) : ℝ) ≤ ((3269249537800809 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2040 : ((199551000342081253 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((255 / 8 : ℚ) : ℝ) ∧
    heightZ ((255 / 8 : ℚ) : ℝ) ≤ ((399102000684162509 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((199551000342081253 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((255 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-49 / 24 : ℚ) : ℝ) ∧
      Real.exp (-((255 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-49 / 24 : ℚ) : ℝ) ≤ ((399102000684162509 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2040 : ((3218564521646469 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((255 / 8 : ℚ) : ℝ) ∧
    logKernel ((255 / 8 : ℚ) : ℝ) ≤ ((1609282260823237 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2040
  constructor
  · exact (show ((3218564521646469 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((199551000342081253 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((255 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((399102000684162509 / 18446744073709551616 : ℚ) : ℝ) ≤ ((1609282260823237 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2041 : ((392914497675288055 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2041 / 64 : ℚ) : ℝ) ∧
    heightZ ((2041 / 64 : ℚ) : ℝ) ≤ ((196457248837644029 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((392914497675288055 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2041 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-395 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2041 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-395 / 192 : ℚ) : ℝ) ≤ ((196457248837644029 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2041 : ((1584332651916483 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2041 / 64 : ℚ) : ℝ) ∧
    logKernel ((2041 / 64 : ℚ) : ℝ) ≤ ((3168665303832971 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2041
  constructor
  · exact (show ((1584332651916483 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((392914497675288055 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2041 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((196457248837644029 / 9223372036854775808 : ℚ) : ℝ) ≤ ((3168665303832971 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2042 : ((386822923009090915 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1021 / 32 : ℚ) : ℝ) ∧
    heightZ ((1021 / 32 : ℚ) : ℝ) ≤ ((193411461504545459 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((386822923009090915 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1021 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-199 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1021 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-199 / 96 : ℚ) : ℝ) ≤ ((193411461504545459 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2042 : ((3119539701686215 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1021 / 32 : ℚ) : ℝ) ∧
    logKernel ((1021 / 32 : ℚ) : ℝ) ≤ ((779884925421555 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2042
  constructor
  · exact (show ((3119539701686215 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((386822923009090915 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1021 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((193411461504545459 / 9223372036854775808 : ℚ) : ℝ) ≤ ((779884925421555 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2043 : ((380825789454467419 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2043 / 64 : ℚ) : ℝ) ∧
    heightZ ((2043 / 64 : ℚ) : ℝ) ≤ ((190412894727233711 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((380825789454467419 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2043 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-401 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2043 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-401 / 192 : ℚ) : ℝ) ≤ ((190412894727233711 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2043 : ((3071175721406993 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2043 / 64 : ℚ) : ℝ) ∧
    logKernel ((2043 / 64 : ℚ) : ℝ) ≤ ((1535587860703499 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2043
  constructor
  · exact (show ((3071175721406993 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((380825789454467419 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2043 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((190412894727233711 / 9223372036854775808 : ℚ) : ℝ) ≤ ((1535587860703499 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2044 : ((374921632837695009 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((511 / 16 : ℚ) : ℝ) ∧
    heightZ ((511 / 16 : ℚ) : ℝ) ≤ ((93730408209423753 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((374921632837695009 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((511 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-101 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((511 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-101 / 48 : ℚ) : ℝ) ≤ ((93730408209423753 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2044 : ((3023561555142699 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((511 / 16 : ℚ) : ℝ) ∧
    logKernel ((511 / 16 : ℚ) : ℝ) ≤ ((188972597196419 / 4503599627370496 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2044
  constructor
  · exact (show ((3023561555142699 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((374921632837695009 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((511 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((93730408209423753 / 4611686018427387904 : ℚ) : ℝ) ≤ ((188972597196419 / 4503599627370496 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2045 : ((46138626460620083 / 2305843009213693952 : ℚ) : ℝ) ≤ heightZ ((2045 / 64 : ℚ) : ℝ) ∧
    heightZ ((2045 / 64 : ℚ) : ℝ) ≤ ((369109011684960667 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((46138626460620083 / 2305843009213693952 : ℚ) : ℝ) ≤ Real.exp (-((2045 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-407 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2045 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-407 / 192 : ℚ) : ℝ) ≤ ((369109011684960667 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2045 : ((2976685578104519 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2045 / 64 : ℚ) : ℝ) ∧
    logKernel ((2045 / 64 : ℚ) : ℝ) ≤ ((744171394526131 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2045
  constructor
  · exact (show ((2976685578104519 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((46138626460620083 / 2305843009213693952 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2045 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((369109011684960667 / 18446744073709551616 : ℚ) : ℝ) ≤ ((744171394526131 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2046 : ((363386506870431431 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1023 / 32 : ℚ) : ℝ) ∧
    heightZ ((1023 / 32 : ℚ) : ℝ) ≤ ((181693253435215717 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((363386506870431431 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1023 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-205 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1023 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-205 / 96 : ℚ) : ℝ) ≤ ((181693253435215717 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2046 : ((2930536345729283 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1023 / 32 : ℚ) : ℝ) ∧
    logKernel ((1023 / 32 : ℚ) : ℝ) ≤ ((366317043216161 / 9007199254740992 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2046
  constructor
  · exact (show ((2930536345729283 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((363386506870431431 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1023 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((181693253435215717 / 9223372036854775808 : ℚ) : ℝ) ≤ ((366317043216161 / 9007199254740992 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2047 : ((178876360634890553 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2047 / 64 : ℚ) : ℝ) ∧
    heightZ ((2047 / 64 : ℚ) : ℝ) ≤ ((357752721269781109 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((178876360634890553 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2047 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-413 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2047 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-413 / 192 : ℚ) : ℝ) ≤ ((357752721269781109 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2047 : ((2885102590885329 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2047 / 64 : ℚ) : ℝ) ∧
    logKernel ((2047 / 64 : ℚ) : ℝ) ≤ ((1442551295442667 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2047
  constructor
  · exact (show ((2885102590885329 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((178876360634890553 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2047 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((357752721269781109 / 18446744073709551616 : ℚ) : ℝ) ≤ ((1442551295442667 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2048 : ((352206279419088487 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((32 / 1 : ℚ) : ℝ) ∧
    heightZ ((32 / 1 : ℚ) : ℝ) ≤ ((176103139709544245 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((352206279419088487 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((32 / 1 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-13 / 6 : ℚ) : ℝ) ∧
      Real.exp (-((32 / 1 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-13 / 6 : ℚ) : ℝ) ≤ ((176103139709544245 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2048 : ((2840373221121679 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((32 / 1 : ℚ) : ℝ) ∧
    logKernel ((32 / 1 : ℚ) : ℝ) ≤ ((710093305280421 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2048
  constructor
  · exact (show ((2840373221121679 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((352206279419088487 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((32 / 1 : ℚ) : ℝ)) hh).trans
      (show zKernel ((176103139709544245 / 9223372036854775808 : ℚ) : ℝ) ≤ ((710093305280421 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2049 : ((21671614198688995 / 1152921504606846976 : ℚ) : ℝ) ≤ heightZ ((2049 / 64 : ℚ) : ℝ) ∧
    heightZ ((2049 / 64 : ℚ) : ℝ) ≤ ((346745827179023923 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((21671614198688995 / 1152921504606846976 : ℚ) : ℝ) ≤ Real.exp (-((2049 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-419 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2049 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-419 / 192 : ℚ) : ℝ) ≤ ((346745827179023923 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2049 : ((699084328989967 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((2049 / 64 : ℚ) : ℝ) ∧
    logKernel ((2049 / 64 : ℚ) : ℝ) ≤ ((2796337315959873 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2049
  constructor
  · exact (show ((699084328989967 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((21671614198688995 / 1152921504606846976 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2049 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((346745827179023923 / 18446744073709551616 : ℚ) : ℝ) ≤ ((2796337315959873 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2050 : ((42671253925530269 / 2305843009213693952 : ℚ) : ℝ) ≤ heightZ ((1025 / 32 : ℚ) : ℝ) ∧
    heightZ ((1025 / 32 : ℚ) : ℝ) ≤ ((341370031404242155 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((42671253925530269 / 2305843009213693952 : ℚ) : ℝ) ≤ Real.exp (-((1025 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-211 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1025 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-211 / 96 : ℚ) : ℝ) ≤ ((341370031404242155 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2050 : ((2752984124227757 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1025 / 32 : ℚ) : ℝ) ∧
    logKernel ((1025 / 32 : ℚ) : ℝ) ≤ ((1376492062113881 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2050
  constructor
  · exact (show ((2752984124227757 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((42671253925530269 / 2305843009213693952 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1025 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((341370031404242155 / 18446744073709551616 : ℚ) : ℝ) ≤ ((1376492062113881 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2051 : ((336077579617900773 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2051 / 64 : ℚ) : ℝ) ∧
    heightZ ((2051 / 64 : ℚ) : ℝ) ≤ ((42009697452237597 / 2305843009213693952 : ℚ) : ℝ) := by
  have h : ((336077579617900773 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2051 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-425 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2051 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-425 / 192 : ℚ) : ℝ) ≤ ((42009697452237597 / 2305843009213693952 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2051 : ((2710303061434681 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2051 / 64 : ℚ) : ℝ) ∧
    logKernel ((2051 / 64 : ℚ) : ℝ) ≤ ((1355151530717343 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2051
  constructor
  · exact (show ((2710303061434681 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((336077579617900773 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2051 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((42009697452237597 / 2305843009213693952 : ℚ) : ℝ) ≤ ((1355151530717343 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2052 : ((330867179691224777 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((513 / 16 : ℚ) : ℝ) ∧
    heightZ ((513 / 16 : ℚ) : ℝ) ≤ ((82716794922806195 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((330867179691224777 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((513 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-107 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((513 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-107 / 48 : ℚ) : ℝ) ≤ ((82716794922806195 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2052 : ((1334141853593647 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((513 / 16 : ℚ) : ℝ) ∧
    logKernel ((513 / 16 : ℚ) : ℝ) ≤ ((2668283707187299 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2052
  constructor
  · exact (show ((1334141853593647 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((330867179691224777 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((513 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((82716794922806195 / 4611686018427387904 : ℚ) : ℝ) ≤ ((2668283707187299 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2053 : ((325737559528039017 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2053 / 64 : ℚ) : ℝ) ∧
    heightZ ((2053 / 64 : ℚ) : ℝ) ≤ ((81434389882009755 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((325737559528039017 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2053 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-431 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2053 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-431 / 192 : ℚ) : ℝ) ≤ ((81434389882009755 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2053 : ((2626915802645473 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2053 / 64 : ℚ) : ℝ) ∧
    logKernel ((2053 / 64 : ℚ) : ℝ) ≤ ((1313457901322739 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2053
  constructor
  · exact (show ((2626915802645473 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((325737559528039017 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2053 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((81434389882009755 / 4611686018427387904 : ℚ) : ℝ) ≤ ((1313457901322739 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2054 : ((320687466754191535 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1027 / 32 : ℚ) : ℝ) ∧
    heightZ ((1027 / 32 : ℚ) : ℝ) ≤ ((160343733377095769 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((320687466754191535 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1027 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-217 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1027 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-217 / 96 : ℚ) : ℝ) ≤ ((160343733377095769 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2054 : ((2586189248017671 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1027 / 32 : ℚ) : ℝ) ∧
    logKernel ((1027 / 32 : ℚ) : ℝ) ≤ ((646547312004419 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2054
  constructor
  · exact (show ((2586189248017671 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((320687466754191535 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1027 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((160343733377095769 / 9223372036854775808 : ℚ) : ℝ) ≤ ((646547312004419 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2055 : ((315715668411791929 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2055 / 64 : ℚ) : ℝ) ∧
    heightZ ((2055 / 64 : ℚ) : ℝ) ≤ ((78928917102947983 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((315715668411791929 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2055 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-437 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2055 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-437 / 192 : ℚ) : ℝ) ≤ ((78928917102947983 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2055 : ((1273047050047547 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2055 / 64 : ℚ) : ℝ) ∧
    logKernel ((2055 / 64 : ℚ) : ℝ) ≤ ((2546094100095099 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2055
  constructor
  · exact (show ((1273047050047547 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((315715668411791929 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2055 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((78928917102947983 / 4611686018427387904 : ℚ) : ℝ) ≤ ((2546094100095099 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2056 : ((310820950658190121 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((257 / 8 : ℚ) : ℝ) ∧
    heightZ ((257 / 8 : ℚ) : ℝ) ≤ ((77705237664547531 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((310820950658190121 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((257 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-55 / 24 : ℚ) : ℝ) ∧
      Real.exp (-((257 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-55 / 24 : ℚ) : ℝ) ≤ ((77705237664547531 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2056 : ((2506620569824111 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((257 / 8 : ℚ) : ℝ) ∧
    logKernel ((257 / 8 : ℚ) : ℝ) ≤ ((626655142456029 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2056
  constructor
  · exact (show ((2506620569824111 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((310820950658190121 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((257 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((77705237664547531 / 4611686018427387904 : ℚ) : ℝ) ≤ ((626655142456029 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2057 : ((306002118469622025 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2057 / 64 : ℚ) : ℝ) ∧
    heightZ ((2057 / 64 : ℚ) : ℝ) ≤ ((76500529617405507 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((306002118469622025 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2057 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-443 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2057 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-443 / 192 : ℚ) : ℝ) ≤ ((76500529617405507 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2057 : ((154234938744769 / 4503599627370496 : ℚ) : ℝ) ≤ logKernel ((2057 / 64 : ℚ) : ℝ) ∧
    logKernel ((2057 / 64 : ℚ) : ℝ) ≤ ((2467759019916309 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2057
  constructor
  · exact (show ((154234938744769 / 4503599627370496 : ℚ) : ℝ) ≤ zKernel ((306002118469622025 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2057 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((76500529617405507 / 4611686018427387904 : ℚ) : ℝ) ≤ ((2467759019916309 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2058 : ((9414312354670305 / 576460752303423488 : ℚ) : ℝ) ≤ heightZ ((1029 / 32 : ℚ) : ℝ) ∧
    heightZ ((1029 / 32 : ℚ) : ℝ) ≤ ((301257995349449763 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((9414312354670305 / 576460752303423488 : ℚ) : ℝ) ≤ Real.exp (-((1029 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-223 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1029 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-223 / 96 : ℚ) : ℝ) ≤ ((301257995349449763 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2058 : ((303687495311945 / 9007199254740992 : ℚ) : ℝ) ≤ logKernel ((1029 / 32 : ℚ) : ℝ) ∧
    logKernel ((1029 / 32 : ℚ) : ℝ) ≤ ((2429499962495565 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2058
  constructor
  · exact (show ((303687495311945 / 9007199254740992 : ℚ) : ℝ) ≤ zKernel ((9414312354670305 / 576460752303423488 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1029 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((301257995349449763 / 18446744073709551616 : ℚ) : ℝ) ≤ ((2429499962495565 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2059 : ((579272310626807 / 36028797018963968 : ℚ) : ℝ) ≤ heightZ ((2059 / 64 : ℚ) : ℝ) ∧
    heightZ ((2059 / 64 : ℚ) : ℝ) ≤ ((296587423040925187 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((579272310626807 / 36028797018963968 : ℚ) : ℝ) ≤ Real.exp (-((2059 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-449 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2059 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-449 / 192 : ℚ) : ℝ) ≤ ((296587423040925187 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2059 : ((597958514195413 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((2059 / 64 : ℚ) : ℝ) ∧
    logKernel ((2059 / 64 : ℚ) : ℝ) ≤ ((2391834056781657 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2059
  constructor
  · exact (show ((597958514195413 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((579272310626807 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2059 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((296587423040925187 / 18446744073709551616 : ℚ) : ℝ) ≤ ((2391834056781657 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2060 : ((145994630622203307 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((515 / 16 : ℚ) : ℝ) ∧
    heightZ ((515 / 16 : ℚ) : ℝ) ≤ ((291989261244406617 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((145994630622203307 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((515 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-113 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((515 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-113 / 48 : ℚ) : ℝ) ≤ ((291989261244406617 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2060 : ((18396500834451 / 562949953421312 : ℚ) : ℝ) ≤ logKernel ((515 / 16 : ℚ) : ℝ) ∧
    logKernel ((515 / 16 : ℚ) : ℝ) ≤ ((2354752106809733 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2060
  constructor
  · exact (show ((18396500834451 / 562949953421312 : ℚ) : ℝ) ≤ zKernel ((145994630622203307 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((515 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((291989261244406617 / 18446744073709551616 : ℚ) : ℝ) ≤ ((2354752106809733 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2061 : ((143731193669479847 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2061 / 64 : ℚ) : ℝ) ∧
    heightZ ((2061 / 64 : ℚ) : ℝ) ≤ ((287462387338959697 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((143731193669479847 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2061 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-455 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2061 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-455 / 192 : ℚ) : ℝ) ≤ ((287462387338959697 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2061 : ((1156034051732537 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2061 / 64 : ℚ) : ℝ) ∧
    logKernel ((2061 / 64 : ℚ) : ℝ) ≤ ((2312068103465079 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2061
  constructor
  · exact (show ((1156034051732537 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((143731193669479847 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2061 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((287462387338959697 / 18446744073709551616 : ℚ) : ℝ) ≤ ((2312068103465079 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2062 : ((283005696108274443 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1031 / 32 : ℚ) : ℝ) ∧
    heightZ ((1031 / 32 : ℚ) : ℝ) ≤ ((141502848054137223 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((283005696108274443 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1031 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-229 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1031 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-229 / 96 : ℚ) : ℝ) ≤ ((141502848054137223 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2062 : ((70029163945345 / 2251799813685248 : ℚ) : ℝ) ≤ logKernel ((1031 / 32 : ℚ) : ℝ) ∧
    logKernel ((1031 / 32 : ℚ) : ℝ) ≤ ((2240933246251045 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2062
  constructor
  · exact (show ((70029163945345 / 2251799813685248 : ℚ) : ℝ) ≤ zKernel ((283005696108274443 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1031 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((141502848054137223 / 9223372036854775808 : ℚ) : ℝ) ≤ ((2240933246251045 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2063 : ((278618099470831565 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2063 / 64 : ℚ) : ℝ) ∧
    heightZ ((2063 / 64 : ℚ) : ℝ) ≤ ((17413631216926973 / 1152921504606846976 : ℚ) : ℝ) := by
  have h : ((278618099470831565 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2063 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-461 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2063 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-461 / 192 : ℚ) : ℝ) ≤ ((17413631216926973 / 1152921504606846976 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2063 : ((2171986978509469 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2063 / 64 : ℚ) : ℝ) ∧
    logKernel ((2063 / 64 : ℚ) : ℝ) ≤ ((1085993489254737 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2063
  constructor
  · exact (show ((2171986978509469 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((278618099470831565 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2063 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((17413631216926973 / 1152921504606846976 : ℚ) : ℝ) ≤ ((1085993489254737 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2064 : ((274298526214252141 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((129 / 4 : ℚ) : ℝ) ∧
    heightZ ((129 / 4 : ℚ) : ℝ) ≤ ((17143657888390759 / 1152921504606846976 : ℚ) : ℝ) := by
  have h : ((274298526214252141 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((129 / 4 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-29 / 12 : ℚ) : ℝ) ∧
      Real.exp (-((129 / 4 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-29 / 12 : ℚ) : ℝ) ≤ ((17143657888390759 / 1152921504606846976 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2064 : ((1052580982210617 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((129 / 4 : ℚ) : ℝ) ∧
    logKernel ((129 / 4 : ℚ) : ℝ) ≤ ((2105161964421239 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2064
  constructor
  · exact (show ((1052580982210617 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((274298526214252141 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((129 / 4 : ℚ) : ℝ)) hh).trans
      (show zKernel ((17143657888390759 / 1152921504606846976 : ℚ) : ℝ) ≤ ((2105161964421239 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2065 : ((135022960866882925 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2065 / 64 : ℚ) : ℝ) ∧
    heightZ ((2065 / 64 : ℚ) : ℝ) ≤ ((270045921733765853 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((135022960866882925 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2065 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-467 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2065 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-467 / 192 : ℚ) : ℝ) ≤ ((270045921733765853 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2065 : ((2040392939872567 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2065 / 64 : ℚ) : ℝ) ∧
    logKernel ((2065 / 64 : ℚ) : ℝ) ≤ ((510098234968143 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2065
  constructor
  · exact (show ((2040392939872567 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((135022960866882925 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2065 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((270045921733765853 / 18446744073709551616 : ℚ) : ℝ) ≤ ((510098234968143 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem log_height_bounds_192 : ((249238318177856223 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1017 / 32 : ℚ) : ℝ) ∧
    Real.log ((1017 / 32 : ℚ) : ℝ) ≤ ((124619159088928113 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((249238318177856223 / 72057594037927936 : ℚ) : ℝ) ≤ ((1017 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1017 / 32 : ℚ) : ℝ) ≤ Real.exp ((124619159088928113 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_192 : heightPower (192 : Fin 988) ≤ ((218108027656715 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_192
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_192 : heightFactor (192 : Fin 988) ≤ ((1234313488321509 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_192
  obtain ⟨hpl, hph⟩ := kernel_bounds_2033
  obtain ⟨hcl, hch⟩ := kernel_bounds_2034
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2034
  have h : (((1034289 / 512 : ℚ) : ℝ) * (logKernel ((2033 / 64 : ℚ) : ℝ) - logKernel ((1017 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1017 / 32 : ℚ) : ℝ) + Real.log ((1017 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1234313488321509 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_193 : ((249273736017860473 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2035 / 64 : ℚ) : ℝ) ∧
    Real.log ((2035 / 64 : ℚ) : ℝ) ≤ ((62318434004465119 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((249273736017860473 / 72057594037927936 : ℚ) : ℝ) ≤ ((2035 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2035 / 64 : ℚ) : ℝ) ≤ Real.exp ((62318434004465119 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_193 : heightPower (193 : Fin 988) ≤ ((876968508075481 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_193
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_193 : heightFactor (193 : Fin 988) ≤ ((1222924537367267 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_193
  obtain ⟨hpl, hph⟩ := kernel_bounds_2034
  obtain ⟨hcl, hch⟩ := kernel_bounds_2035
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2035
  have h : (((4141225 / 2048 : ℚ) : ℝ) * (logKernel ((1017 / 32 : ℚ) : ℝ) - logKernel ((2035 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2035 / 64 : ℚ) : ℝ) + Real.log ((2035 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1222924537367267 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_194 : ((124654568228897621 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((509 / 16 : ℚ) : ℝ) ∧
    Real.log ((509 / 16 : ℚ) : ℝ) ≤ ((249309136457795245 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((124654568228897621 / 36028797018963968 : ℚ) : ℝ) ≤ ((509 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((509 / 16 : ℚ) : ℝ) ≤ Real.exp ((249309136457795245 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_194 : heightPower (194 : Fin 988) ≤ ((110188104694385 / 35184372088832 : ℚ) : ℝ) := by
  have hh := log_height_bounds_194
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_194 : heightFactor (194 : Fin 988) ≤ ((1211639989026381 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_194
  obtain ⟨hpl, hph⟩ := kernel_bounds_2035
  obtain ⟨hcl, hch⟩ := kernel_bounds_2036
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2036
  have h : (((259081 / 128 : ℚ) : ℝ) * (logKernel ((2035 / 64 : ℚ) : ℝ) - logKernel ((509 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((509 / 16 : ℚ) : ℝ) + Real.log ((509 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1211639989026381 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_195 : ((249344519514748739 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2037 / 64 : ℚ) : ℝ) ∧
    Real.log ((2037 / 64 : ℚ) : ℝ) ≤ ((124672259757374371 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((249344519514748739 / 72057594037927936 : ℚ) : ℝ) ≤ ((2037 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2037 / 64 : ℚ) : ℝ) ≤ Real.exp ((124672259757374371 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_195 : heightPower (195 : Fin 988) ≤ ((886041099132409 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_195
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_195 : heightFactor (195 : Fin 988) ≤ ((600229446622315 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_195
  obtain ⟨hpl, hph⟩ := kernel_bounds_2036
  obtain ⟨hcl, hch⟩ := kernel_bounds_2037
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2037
  have h : (((4149369 / 2048 : ℚ) : ℝ) * (logKernel ((509 / 16 : ℚ) : ℝ) - logKernel ((2037 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2037 / 64 : ℚ) : ℝ) + Real.log ((2037 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((600229446622315 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_196 : ((249379885205784017 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1019 / 32 : ℚ) : ℝ) ∧
    Real.log ((1019 / 32 : ℚ) : ℝ) ≤ ((62344971301446005 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((249379885205784017 / 72057594037927936 : ℚ) : ℝ) ≤ ((1019 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1019 / 32 : ℚ) : ℝ) ≤ Real.exp ((62344971301446005 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_196 : heightPower (196 : Fin 988) ≤ ((890577292874119 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_196
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_196 : heightFactor (196 : Fin 988) ≤ ((148672538567659 / 35184372088832 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_196
  obtain ⟨hpl, hph⟩ := kernel_bounds_2037
  obtain ⟨hcl, hch⟩ := kernel_bounds_2038
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2038
  have h : (((1038361 / 512 : ℚ) : ℝ) * (logKernel ((2037 / 64 : ℚ) : ℝ) - logKernel ((1019 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1019 / 32 : ℚ) : ℝ) + Real.log ((1019 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((148672538567659 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_197 : ((62353808386984753 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((2039 / 64 : ℚ) : ℝ) ∧
    Real.log ((2039 / 64 : ℚ) : ℝ) ≤ ((249415233547939015 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((62353808386984753 / 18014398509481984 : ℚ) : ℝ) ≤ ((2039 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2039 / 64 : ℚ) : ℝ) ≤ Real.exp ((249415233547939015 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_197 : heightPower (197 : Fin 988) ≤ ((447556709423383 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_197
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_197 : heightFactor (197 : Fin 988) ≤ ((1178403301932413 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_197
  obtain ⟨hpl, hph⟩ := kernel_bounds_2038
  obtain ⟨hcl, hch⟩ := kernel_bounds_2039
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2039
  have h : (((4157521 / 2048 : ℚ) : ℝ) * (logKernel ((1019 / 32 : ℚ) : ℝ) - logKernel ((2039 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2039 / 64 : ℚ) : ℝ) + Real.log ((2039 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1178403301932413 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_198 : ((62362641139556651 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((255 / 8 : ℚ) : ℝ) ∧
    Real.log ((255 / 8 : ℚ) : ℝ) ≤ ((249450564558226607 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((62362641139556651 / 18014398509481984 : ℚ) : ℝ) ≤ ((255 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((255 / 8 : ℚ) : ℝ) ≤ Real.exp ((249450564558226607 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_198 : heightPower (198 : Fin 988) ≤ ((449824738558403 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_198
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_198 : heightFactor (198 : Fin 988) ≤ ((1167526948855061 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_198
  obtain ⟨hpl, hph⟩ := kernel_bounds_2039
  obtain ⟨hcl, hch⟩ := kernel_bounds_2040
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2040
  have h : (((65025 / 32 : ℚ) : ℝ) * (logKernel ((2039 / 64 : ℚ) : ℝ) - logKernel ((255 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((255 / 8 : ℚ) : ℝ) + Real.log ((255 / 8 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1167526948855061 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_199 : ((124742939126817327 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2041 / 64 : ℚ) : ℝ) ∧
    Real.log ((2041 / 64 : ℚ) : ℝ) ≤ ((249485878253634657 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((124742939126817327 / 36028797018963968 : ℚ) : ℝ) ≤ ((2041 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2041 / 64 : ℚ) : ℝ) ≤ Real.exp ((249485878253634657 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_199 : heightPower (199 : Fin 988) ≤ ((452092733875299 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_199
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_199 : heightFactor (199 : Fin 988) ≤ ((289187583272959 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_199
  obtain ⟨hpl, hph⟩ := kernel_bounds_2040
  obtain ⟨hcl, hch⟩ := kernel_bounds_2041
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2041
  have h : (((4165681 / 2048 : ℚ) : ℝ) * (logKernel ((255 / 8 : ℚ) : ℝ) - logKernel ((2041 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2041 / 64 : ℚ) : ℝ) + Real.log ((2041 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((289187583272959 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_200 : ((249521174651126065 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1021 / 32 : ℚ) : ℝ) ∧
    Real.log ((1021 / 32 : ℚ) : ℝ) ≤ ((62380293662781517 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((249521174651126065 / 72057594037927936 : ℚ) : ℝ) ≤ ((1021 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1021 / 32 : ℚ) : ℝ) ≤ Real.exp ((62380293662781517 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_200 : heightPower (200 : Fin 988) ≤ ((908721390814403 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_200
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_200 : heightFactor (200 : Fin 988) ≤ ((573036273348181 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_200
  obtain ⟨hpl, hph⟩ := kernel_bounds_2041
  obtain ⟨hcl, hch⟩ := kernel_bounds_2042
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2042
  have h : (((1042441 / 512 : ℚ) : ℝ) * (logKernel ((2041 / 64 : ℚ) : ℝ) - logKernel ((1021 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1021 / 32 : ℚ) : ℝ) + Real.log ((1021 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((573036273348181 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_201 : ((249556453767638821 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2043 / 64 : ℚ) : ℝ) ∧
    Real.log ((2043 / 64 : ℚ) : ℝ) ≤ ((31194556720954853 / 9007199254740992 : ℚ) : ℝ) := by
  have hl : Real.exp ((249556453767638821 / 72057594037927936 : ℚ) : ℝ) ≤ ((2043 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2043 / 64 : ℚ) : ℝ) ≤ Real.exp ((31194556720954853 / 9007199254740992 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_201 : heightPower (201 : Fin 988) ≤ ((913257246374385 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_201
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_201 : heightFactor (201 : Fin 988) ≤ ((567746344959653 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_201
  obtain ⟨hpl, hph⟩ := kernel_bounds_2042
  obtain ⟨hcl, hch⟩ := kernel_bounds_2043
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2043
  have h : (((4173849 / 2048 : ℚ) : ℝ) * (logKernel ((1021 / 32 : ℚ) : ℝ) - logKernel ((2043 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2043 / 64 : ℚ) : ℝ) + Real.log ((2043 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((567746344959653 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_202 : ((124795857810043021 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((511 / 16 : ℚ) : ℝ) ∧
    Real.log ((511 / 16 : ℚ) : ℝ) ≤ ((249591715620086045 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((124795857810043021 / 36028797018963968 : ℚ) : ℝ) ≤ ((511 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((511 / 16 : ℚ) : ℝ) ≤ Real.exp ((249591715620086045 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_202 : heightPower (202 : Fin 988) ≤ ((917793034496611 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_202
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_202 : heightFactor (202 : Fin 988) ≤ ((562504935567541 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_202
  obtain ⟨hpl, hph⟩ := kernel_bounds_2043
  obtain ⟨hcl, hch⟩ := kernel_bounds_2044
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2044
  have h : (((261121 / 128 : ℚ) : ℝ) * (logKernel ((2043 / 64 : ℚ) : ℝ) - logKernel ((511 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((511 / 16 : ℚ) : ℝ) + Real.log ((511 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((562504935567541 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_203 : ((124813480112678015 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2045 / 64 : ℚ) : ℝ) ∧
    Real.log ((2045 / 64 : ℚ) : ℝ) ≤ ((249626960225356033 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((124813480112678015 / 36028797018963968 : ℚ) : ℝ) ≤ ((2045 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2045 / 64 : ℚ) : ℝ) ≤ Real.exp ((249626960225356033 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_203 : heightPower (203 : Fin 988) ≤ ((461164377623525 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_203
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_203 : heightFactor (203 : Fin 988) ≤ ((1114623206769191 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_203
  obtain ⟨hpl, hph⟩ := kernel_bounds_2044
  obtain ⟨hcl, hch⟩ := kernel_bounds_2045
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2045
  have h : (((4182025 / 2048 : ℚ) : ℝ) * (logKernel ((511 / 16 : ℚ) : ℝ) - logKernel ((2045 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2045 / 64 : ℚ) : ℝ) + Real.log ((2045 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1114623206769191 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_204 : ((249662187600312317 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1023 / 32 : ℚ) : ℝ) ∧
    Real.log ((1023 / 32 : ℚ) : ℝ) ≤ ((121905365039215 / 35184372088832 : ℚ) : ℝ) := by
  have hl : Real.exp ((249662187600312317 / 72057594037927936 : ℚ) : ℝ) ≤ ((1023 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1023 / 32 : ℚ) : ℝ) ≤ Real.exp ((121905365039215 / 35184372088832 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_204 : heightPower (204 : Fin 988) ≤ ((926864408691577 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_204
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_204 : heightFactor (204 : Fin 988) ≤ ((1104331821226215 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_204
  obtain ⟨hpl, hph⟩ := kernel_bounds_2045
  obtain ⟨hcl, hch⟩ := kernel_bounds_2046
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2046
  have h : (((1046529 / 512 : ℚ) : ℝ) * (logKernel ((2045 / 64 : ℚ) : ℝ) - logKernel ((1023 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1023 / 32 : ℚ) : ℝ) + Real.log ((1023 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1104331821226215 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_205 : ((62424349440448429 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((2047 / 64 : ℚ) : ℝ) ∧
    Real.log ((2047 / 64 : ℚ) : ℝ) ≤ ((249697397761793719 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((62424349440448429 / 18014398509481984 : ℚ) : ℝ) ≤ ((2047 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2047 / 64 : ℚ) : ℝ) ≤ Real.exp ((249697397761793719 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_205 : heightPower (205 : Fin 988) ≤ ((29106249840499 / 8796093022208 : ℚ) : ℝ) := by
  have hh := log_height_bounds_205
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_205 : heightFactor (205 : Fin 988) ≤ ((547067423409221 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_205
  obtain ⟨hpl, hph⟩ := kernel_bounds_2046
  obtain ⟨hcl, hch⟩ := kernel_bounds_2047
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2047
  have h : (((4190209 / 2048 : ℚ) : ℝ) * (logKernel ((1023 / 32 : ℚ) : ℝ) - logKernel ((2047 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2047 / 64 : ℚ) : ℝ) + Real.log ((2047 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((547067423409221 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_206 : ((249732590726614367 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((32 / 1 : ℚ) : ℝ) ∧
    Real.log ((32 / 1 : ℚ) : ℝ) ≤ ((124866295363307185 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((249732590726614367 / 72057594037927936 : ℚ) : ℝ) ≤ ((32 / 1 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((32 / 1 : ℚ) : ℝ) ≤ Real.exp ((124866295363307185 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_206 : heightPower (206 : Fin 988) ≤ ((935935513925903 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_206
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_206 : heightFactor (206 : Fin 988) ≤ ((1084031423695121 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_206
  obtain ⟨hpl, hph⟩ := kernel_bounds_2047
  obtain ⟨hcl, hch⟩ := kernel_bounds_2048
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2048
  have h : (((2048 / 1 : ℚ) : ℝ) * (logKernel ((2047 / 64 : ℚ) : ℝ) - logKernel ((32 / 1 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((32 / 1 : ℚ) : ℝ) + Real.log ((32 / 1 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1084031423695121 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_207 : ((124883883255781893 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2049 / 64 : ℚ) : ℝ) ∧
    Real.log ((2049 / 64 : ℚ) : ℝ) ≤ ((249767766511563789 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((124883883255781893 / 36028797018963968 : ℚ) : ℝ) ≤ ((2049 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2049 / 64 : ℚ) : ℝ) ≤ Real.exp ((249767766511563789 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_207 : heightPower (207 : Fin 988) ≤ ((470235482923483 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_207
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_207 : heightFactor (207 : Fin 988) ≤ ((1074020699772351 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_207
  obtain ⟨hpl, hph⟩ := kernel_bounds_2048
  obtain ⟨hcl, hch⟩ := kernel_bounds_2049
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2049
  have h : (((4198401 / 2048 : ℚ) : ℝ) * (logKernel ((32 / 1 : ℚ) : ℝ) - logKernel ((2049 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2049 / 64 : ℚ) : ℝ) + Real.log ((2049 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1074020699772351 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_208 : ((249802925133406913 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1025 / 32 : ℚ) : ℝ) ∧
    Real.log ((1025 / 32 : ℚ) : ℝ) ≤ ((62450731283351729 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((249802925133406913 / 72057594037927936 : ℚ) : ℝ) ≤ ((1025 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1025 / 32 : ℚ) : ℝ) ≤ Real.exp ((62450731283351729 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_208 : heightPower (208 : Fin 988) ≤ ((236251587681161 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_208
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_208 : heightFactor (208 : Fin 988) ≤ ((266025457665895 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_208
  obtain ⟨hpl, hph⟩ := kernel_bounds_2049
  obtain ⟨hcl, hch⟩ := kernel_bounds_2050
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2050
  have h : (((1050625 / 512 : ℚ) : ℝ) * (logKernel ((2049 / 64 : ℚ) : ℝ) - logKernel ((1025 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1025 / 32 : ℚ) : ℝ) + Real.log ((1025 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((266025457665895 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_209 : ((3903719790763815 / 1125899906842624 : ℚ) : ℝ) ≤ Real.log ((2051 / 64 : ℚ) : ℝ) ∧
    Real.log ((2051 / 64 : ℚ) : ℝ) ≤ ((249838066608884163 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((3903719790763815 / 1125899906842624 : ℚ) : ℝ) ≤ ((2051 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2051 / 64 : ℚ) : ℝ) ≤ Real.exp ((249838066608884163 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_209 : heightPower (209 : Fin 988) ≤ ((949541668624331 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_209
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_209 : heightFactor (209 : Fin 988) ≤ ((1054273979610725 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_209
  obtain ⟨hpl, hph⟩ := kernel_bounds_2050
  obtain ⟨hcl, hch⟩ := kernel_bounds_2051
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2051
  have h : (((4206601 / 2048 : ℚ) : ℝ) * (logKernel ((1025 / 32 : ℚ) : ℝ) - logKernel ((2051 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2051 / 64 : ℚ) : ℝ) + Real.log ((2051 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1054273979610725 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_210 : ((124936595477355729 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((513 / 16 : ℚ) : ℝ) ∧
    Real.log ((513 / 16 : ℚ) : ℝ) ≤ ((249873190954711461 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((124936595477355729 / 36028797018963968 : ℚ) : ℝ) ≤ ((513 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((513 / 16 : ℚ) : ℝ) ≤ Real.exp ((249873190954711461 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_210 : heightPower (210 : Fin 988) ≤ ((954076919611323 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_210
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_210 : heightFactor (210 : Fin 988) ≤ ((32641759919247 / 8796093022208 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_210
  obtain ⟨hpl, hph⟩ := kernel_bounds_2051
  obtain ⟨hcl, hch⟩ := kernel_bounds_2052
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2052
  have h : (((263169 / 128 : ℚ) : ℝ) * (logKernel ((2051 / 64 : ℚ) : ℝ) - logKernel ((513 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((513 / 16 : ℚ) : ℝ) + Real.log ((513 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((32641759919247 / 8796093022208 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_211 : ((62477074546895077 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((2053 / 64 : ℚ) : ℝ) ∧
    Real.log ((2053 / 64 : ℚ) : ℝ) ≤ ((249908298187580311 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((62477074546895077 / 18014398509481984 : ℚ) : ℝ) ≤ ((2053 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2053 / 64 : ℚ) : ℝ) ≤ Real.exp ((249908298187580311 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_211 : heightPower (211 : Fin 988) ≤ ((958612103750821 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_211
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_211 : heightFactor (211 : Fin 988) ≤ ((258722005593441 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_211
  obtain ⟨hpl, hph⟩ := kernel_bounds_2052
  obtain ⟨hcl, hch⟩ := kernel_bounds_2053
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2053
  have h : (((4214809 / 2048 : ℚ) : ℝ) * (logKernel ((513 / 16 : ℚ) : ℝ) - logKernel ((2053 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2053 / 64 : ℚ) : ℝ) + Real.log ((2053 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((258722005593441 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_212 : ((124971694162078911 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((1027 / 32 : ℚ) : ℝ) ∧
    Real.log ((1027 / 32 : ℚ) : ℝ) ≤ ((249943388324157825 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((124971694162078911 / 36028797018963968 : ℚ) : ℝ) ≤ ((1027 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1027 / 32 : ℚ) : ℝ) ≤ Real.exp ((249943388324157825 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_212 : heightPower (212 : Fin 988) ≤ ((963147221107931 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_212
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_212 : heightFactor (212 : Fin 988) ≤ ((512664140102209 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_212
  obtain ⟨hpl, hph⟩ := kernel_bounds_2053
  obtain ⟨hcl, hch⟩ := kernel_bounds_2054
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2054
  have h : (((1054729 / 512 : ℚ) : ℝ) * (logKernel ((2053 / 64 : ℚ) : ℝ) - logKernel ((1027 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1027 / 32 : ℚ) : ℝ) + Real.log ((1027 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((512664140102209 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_213 : ((249978461381086777 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2055 / 64 : ℚ) : ℝ) ∧
    Real.log ((2055 / 64 : ℚ) : ℝ) ≤ ((62494615345271695 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((249978461381086777 / 72057594037927936 : ℚ) : ℝ) ≤ ((2055 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2055 / 64 : ℚ) : ℝ) ≤ Real.exp ((62494615345271695 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_213 : heightPower (213 : Fin 988) ≤ ((60480141984229 / 17592186044416 : ℚ) : ℝ) := by
  have hh := log_height_bounds_213
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_213 : heightFactor (213 : Fin 988) ≤ ((1015856283986967 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_213
  obtain ⟨hpl, hph⟩ := kernel_bounds_2054
  obtain ⟨hcl, hch⟩ := kernel_bounds_2055
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2055
  have h : (((4223025 / 2048 : ℚ) : ℝ) * (logKernel ((1027 / 32 : ℚ) : ℝ) - logKernel ((2055 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2055 / 64 : ℚ) : ℝ) + Real.log ((2055 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1015856283986967 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_214 : ((250013517374985661 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((257 / 8 : ℚ) : ℝ) ∧
    Real.log ((257 / 8 : ℚ) : ℝ) ≤ ((3906461208984151 / 1125899906842624 : ℚ) : ℝ) := by
  have hl : Real.exp ((250013517374985661 / 72057594037927936 : ℚ) : ℝ) ≤ ((257 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((257 / 8 : ℚ) : ℝ) ≤ Real.exp ((3906461208984151 / 1125899906842624 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_214 : heightPower (214 : Fin 988) ≤ ((972217255734935 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_214
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_214 : heightFactor (214 : Fin 988) ≤ ((1006471234093617 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_214
  obtain ⟨hpl, hph⟩ := kernel_bounds_2055
  obtain ⟨hcl, hch⟩ := kernel_bounds_2056
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2056
  have h : (((66049 / 32 : ℚ) : ℝ) * (logKernel ((2055 / 64 : ℚ) : ℝ) - logKernel ((257 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((257 / 8 : ℚ) : ℝ) + Real.log ((257 / 8 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1006471234093617 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_215 : ((62512139080612179 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((2057 / 64 : ℚ) : ℝ) ∧
    Real.log ((2057 / 64 : ℚ) : ℝ) ≤ ((250048556322448719 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((62512139080612179 / 18014398509481984 : ℚ) : ℝ) ≤ ((2057 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2057 / 64 : ℚ) : ℝ) ≤ Real.exp ((250048556322448719 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_215 : heightPower (215 : Fin 988) ≤ ((976752173134567 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_215
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_215 : heightFactor (215 : Fin 988) ≤ ((124646542265547 / 35184372088832 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_215
  obtain ⟨hpl, hph⟩ := kernel_bounds_2056
  obtain ⟨hcl, hch⟩ := kernel_bounds_2057
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2057
  have h : (((4231249 / 2048 : ℚ) : ℝ) * (logKernel ((257 / 8 : ℚ) : ℝ) - logKernel ((2057 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2057 / 64 : ℚ) : ℝ) + Real.log ((2057 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((124646542265547 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_216 : ((250083578240045991 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1029 / 32 : ℚ) : ℝ) ∧
    Real.log ((1029 / 32 : ℚ) : ℝ) ≤ ((125041789120022997 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((250083578240045991 / 72057594037927936 : ℚ) : ℝ) ≤ ((1029 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1029 / 32 : ℚ) : ℝ) ≤ Real.exp ((125041789120022997 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_216 : heightPower (216 : Fin 988) ≤ ((981287024011285 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_216
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_216 : heightFactor (216 : Fin 988) ≤ ((987958810842333 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_216
  obtain ⟨hpl, hph⟩ := kernel_bounds_2057
  obtain ⟨hcl, hch⟩ := kernel_bounds_2058
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2058
  have h : (((1058841 / 512 : ℚ) : ℝ) * (logKernel ((2057 / 64 : ℚ) : ℝ) - logKernel ((1029 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1029 / 32 : ℚ) : ℝ) + Real.log ((1029 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((987958810842333 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_217 : ((125059291572161693 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2059 / 64 : ℚ) : ℝ) ∧
    Real.log ((2059 / 64 : ℚ) : ℝ) ≤ ((250118583144323389 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((125059291572161693 / 36028797018963968 : ℚ) : ℝ) ≤ ((2059 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2059 / 64 : ℚ) : ℝ) ≤ Real.exp ((250118583144323389 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_217 : heightPower (217 : Fin 988) ≤ ((985821808429723 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_217
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_217 : heightFactor (217 : Fin 988) ≤ ((489414937054751 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_217
  obtain ⟨hpl, hph⟩ := kernel_bounds_2058
  obtain ⟨hcl, hch⟩ := kernel_bounds_2059
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2059
  have h : (((4239481 / 2048 : ℚ) : ℝ) * (logKernel ((1029 / 32 : ℚ) : ℝ) - logKernel ((2059 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2059 / 64 : ℚ) : ℝ) + Real.log ((2059 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((489414937054751 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_218 : ((31269196381475337 / 9007199254740992 : ℚ) : ℝ) ≤ Real.log ((515 / 16 : ℚ) : ℝ) ∧
    Real.log ((515 / 16 : ℚ) : ℝ) ≤ ((250153571051802699 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((31269196381475337 / 9007199254740992 : ℚ) : ℝ) ≤ ((515 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((515 / 16 : ℚ) : ℝ) ≤ Real.exp ((250153571051802699 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_218 : heightPower (218 : Fin 988) ≤ ((495178263227209 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_218
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_218 : heightFactor (218 : Fin 988) ≤ ((484892378411623 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_218
  obtain ⟨hpl, hph⟩ := kernel_bounds_2059
  obtain ⟨hcl, hch⟩ := kernel_bounds_2060
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2060
  have h : (((265225 / 128 : ℚ) : ℝ) * (logKernel ((2059 / 64 : ℚ) : ℝ) - logKernel ((515 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((515 / 16 : ℚ) : ℝ) + Real.log ((515 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((484892378411623 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_219 : ((250188541978981665 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2061 / 64 : ℚ) : ℝ) ∧
    Real.log ((2061 / 64 : ℚ) : ℝ) ≤ ((62547135494745417 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((250188541978981665 / 72057594037927936 : ℚ) : ℝ) ≤ ((2061 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2061 / 64 : ℚ) : ℝ) ≤ Real.exp ((62547135494745417 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_219 : heightPower (219 : Fin 988) ≤ ((994891178149815 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_219
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_219 : heightFactor (219 : Fin 988) ≤ ((1123392927910383 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_219
  obtain ⟨hpl, hph⟩ := kernel_bounds_2060
  obtain ⟨hcl, hch⟩ := kernel_bounds_2061
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2061
  have h : (((4247721 / 2048 : ℚ) : ℝ) * (logKernel ((515 / 16 : ℚ) : ℝ) - logKernel ((2061 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2061 / 64 : ℚ) : ℝ) + Real.log ((2061 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1123392927910383 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_220 : ((250223495942334027 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1031 / 32 : ℚ) : ℝ) ∧
    Real.log ((1031 / 32 : ℚ) : ℝ) ≤ ((125111747971167015 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((250223495942334027 / 72057594037927936 : ℚ) : ℝ) ≤ ((1031 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1031 / 32 : ℚ) : ℝ) ≤ Real.exp ((125111747971167015 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_220 : heightPower (220 : Fin 988) ≤ ((124928220447533 / 35184372088832 : ℚ) : ℝ) := by
  have hh := log_height_bounds_220
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_220 : heightFactor (220 : Fin 988) ≤ ((1884093781574389 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_220
  obtain ⟨hpl, hph⟩ := kernel_bounds_2061
  obtain ⟨hcl, hch⟩ := kernel_bounds_2062
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2062
  have h : (((1062961 / 512 : ℚ) : ℝ) * (logKernel ((2061 / 64 : ℚ) : ℝ) - logKernel ((1031 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1031 / 32 : ℚ) : ℝ) + Real.log ((1031 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1884093781574389 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_221 : ((125129216479154777 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2063 / 64 : ℚ) : ℝ) ∧
    Real.log ((2063 / 64 : ℚ) : ℝ) ≤ ((250258432958309557 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((125129216479154777 / 36028797018963968 : ℚ) : ℝ) ≤ ((2063 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2063 / 64 : ℚ) : ℝ) ≤ Real.exp ((250258432958309557 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_221 : heightPower (221 : Fin 988) ≤ ((501980141405011 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_221
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_221 : heightFactor (221 : Fin 988) ≤ ((1837740079919619 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_221
  obtain ⟨hpl, hph⟩ := kernel_bounds_2062
  obtain ⟨hcl, hch⟩ := kernel_bounds_2063
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2063
  have h : (((4255969 / 2048 : ℚ) : ℝ) * (logKernel ((1031 / 32 : ℚ) : ℝ) - logKernel ((2063 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2063 / 64 : ℚ) : ℝ) + Real.log ((2063 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1837740079919619 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_222 : ((250293353043334103 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((129 / 4 : ℚ) : ℝ) ∧
    Real.log ((129 / 4 : ℚ) : ℝ) ≤ ((125146676521667053 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((250293353043334103 / 72057594037927936 : ℚ) : ℝ) ≤ ((129 / 4 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((129 / 4 : ℚ) : ℝ) ≤ Real.exp ((125146676521667053 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_222 : heightPower (222 : Fin 988) ≤ ((1008494735903253 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_222
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_222 : heightFactor (222 : Fin 988) ≤ ((1792525819454725 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_222
  obtain ⟨hpl, hph⟩ := kernel_bounds_2063
  obtain ⟨hcl, hch⟩ := kernel_bounds_2064
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2064
  have h : (((16641 / 8 : ℚ) : ℝ) * (logKernel ((2063 / 64 : ℚ) : ℝ) - logKernel ((129 / 4 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((129 / 4 : ℚ) : ℝ) + Real.log ((129 / 4 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1792525819454725 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_223 : ((125164128106904831 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2065 / 64 : ℚ) : ℝ) ∧
    Real.log ((2065 / 64 : ℚ) : ℝ) ≤ ((250328256213809665 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((125164128106904831 / 36028797018963968 : ℚ) : ℝ) ≤ ((2065 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2065 / 64 : ℚ) : ℝ) ≤ Real.exp ((250328256213809665 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_223 : heightPower (223 : Fin 988) ≤ ((1013029122924027 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_223
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_223 : heightFactor (223 : Fin 988) ≤ ((1748423016192647 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_223
  obtain ⟨hpl, hph⟩ := kernel_bounds_2064
  obtain ⟨hcl, hch⟩ := kernel_bounds_2065
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2065
  have h : (((4264225 / 2048 : ℚ) : ℝ) * (logKernel ((129 / 4 : ℚ) : ℝ) - logKernel ((2065 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2065 / 64 : ℚ) : ℝ) + Real.log ((2065 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1748423016192647 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

end LegendreK6.M2Pilot.Enclosures.Height006
