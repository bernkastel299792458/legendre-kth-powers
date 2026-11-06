import LegendreK6.M2PilotDefinitions
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp

/-! Generated proposals: every bound is checked by Lean, not by trusting Arb. -/
namespace LegendreK6.M2Pilot.Enclosures.Height004
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem height_z_bounds_1969 : ((605130927961793445 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((1969 / 64 : ℚ) : ℝ) ∧
    heightZ ((1969 / 64 : ℚ) : ℝ) ≤ ((1210261855923586893 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((605130927961793445 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((1969 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-179 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((1969 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-179 / 192 : ℚ) : ℝ) ≤ ((1210261855923586893 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1969 : ((9760176257448279 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1969 / 64 : ℚ) : ℝ) ∧
    logKernel ((1969 / 64 : ℚ) : ℝ) ≤ ((2440044064362071 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1969
  constructor
  · exact (show ((9760176257448279 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((605130927961793445 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1969 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1210261855923586893 / 18446744073709551616 : ℚ) : ℝ) ≤ ((2440044064362071 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1970 : ((1191498485000324225 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((985 / 32 : ℚ) : ℝ) ∧
    heightZ ((985 / 32 : ℚ) : ℝ) ≤ ((297874621250081057 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((1191498485000324225 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((985 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-91 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((985 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-91 / 96 : ℚ) : ℝ) ≤ ((297874621250081057 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1970 : ((2402214687500653 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((985 / 32 : ℚ) : ℝ) ∧
    logKernel ((985 / 32 : ℚ) : ℝ) ≤ ((9608858750002617 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1970
  constructor
  · exact (show ((2402214687500653 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((1191498485000324225 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((985 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((297874621250081057 / 4611686018427387904 : ℚ) : ℝ) ≤ ((9608858750002617 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1971 : ((1173026013180161251 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1971 / 64 : ℚ) : ℝ) ∧
    heightZ ((1971 / 64 : ℚ) : ℝ) ≤ ((586513006590080627 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((1173026013180161251 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1971 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-185 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((1971 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-185 / 192 : ℚ) : ℝ) ≤ ((586513006590080627 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1971 : ((4729943601532907 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((1971 / 64 : ℚ) : ℝ) ∧
    logKernel ((1971 / 64 : ℚ) : ℝ) ≤ ((9459887203065819 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1971
  constructor
  · exact (show ((4729943601532907 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((1173026013180161251 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1971 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((586513006590080627 / 9223372036854775808 : ℚ) : ℝ) ≤ ((9459887203065819 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1972 : ((1154839930490527991 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((493 / 16 : ℚ) : ℝ) ∧
    heightZ ((493 / 16 : ℚ) : ℝ) ≤ ((577419965245263997 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((1154839930490527991 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((493 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-47 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((493 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-47 / 48 : ℚ) : ℝ) ≤ ((577419965245263997 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1972 : ((1164153155736419 / 9007199254740992 : ℚ) : ℝ) ≤ logKernel ((493 / 16 : ℚ) : ℝ) ∧
    logKernel ((493 / 16 : ℚ) : ℝ) ≤ ((9313225245891357 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1972
  constructor
  · exact (show ((1164153155736419 / 9007199254740992 : ℚ) : ℝ) ≤ zKernel ((1154839930490527991 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((493 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((577419965245263997 / 9223372036854775808 : ℚ) : ℝ) ≤ ((9313225245891357 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1973 : ((1136935796879498313 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1973 / 64 : ℚ) : ℝ) ∧
    heightZ ((1973 / 64 : ℚ) : ℝ) ≤ ((284233949219874579 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((1136935796879498313 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1973 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-191 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((1973 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-191 / 192 : ℚ) : ℝ) ≤ ((284233949219874579 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1973 : ((9168837071608855 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1973 / 64 : ℚ) : ℝ) ∧
    logKernel ((1973 / 64 : ℚ) : ℝ) ≤ ((2292209267902215 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1973
  constructor
  · exact (show ((9168837071608855 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((1136935796879498313 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1973 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((284233949219874579 / 4611686018427387904 : ℚ) : ℝ) ≤ ((2292209267902215 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1974 : ((559654620565885409 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((987 / 32 : ℚ) : ℝ) ∧
    heightZ ((987 / 32 : ℚ) : ℝ) ≤ ((1119309241131770821 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((559654620565885409 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((987 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-97 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((987 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-97 / 96 : ℚ) : ℝ) ≤ ((1119309241131770821 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1974 : ((2256671857120505 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((987 / 32 : ℚ) : ℝ) ∧
    logKernel ((987 / 32 : ℚ) : ℝ) ≤ ((9026687428482025 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1974
  constructor
  · exact (show ((2256671857120505 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((559654620565885409 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((987 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1119309241131770821 / 18446744073709551616 : ℚ) : ℝ) ≤ ((9026687428482025 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1975 : ((137744494975181987 / 2305843009213693952 : ℚ) : ℝ) ≤ heightZ ((1975 / 64 : ℚ) : ℝ) ∧
    heightZ ((1975 / 64 : ℚ) : ℝ) ≤ ((1101955959801455899 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((137744494975181987 / 2305843009213693952 : ℚ) : ℝ) ≤ Real.exp (-((1975 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-197 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((1975 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-197 / 192 : ℚ) : ℝ) ≤ ((1101955959801455899 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1975 : ((8886741611302061 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1975 / 64 : ℚ) : ℝ) ∧
    logKernel ((1975 / 64 : ℚ) : ℝ) ≤ ((4443370805651033 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1975
  constructor
  · exact (show ((8886741611302061 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((137744494975181987 / 2305843009213693952 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1975 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1101955959801455899 / 18446744073709551616 : ℚ) : ℝ) ≤ ((4443370805651033 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1976 : ((542435858080704191 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((247 / 8 : ℚ) : ℝ) ∧
    heightZ ((247 / 8 : ℚ) : ℝ) ≤ ((1084871716161408385 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((542435858080704191 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((247 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-25 / 24 : ℚ) : ℝ) ∧
      Real.exp (-((247 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-25 / 24 : ℚ) : ℝ) ≤ ((1084871716161408385 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1976 : ((8748965452914581 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((247 / 8 : ℚ) : ℝ) ∧
    logKernel ((247 / 8 : ℚ) : ℝ) ≤ ((4374482726457293 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1976
  constructor
  · exact (show ((8748965452914581 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((542435858080704191 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((247 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1084871716161408385 / 18446744073709551616 : ℚ) : ℝ) ≤ ((4374482726457293 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1977 : ((66753271198053081 / 1152921504606846976 : ℚ) : ℝ) ≤ heightZ ((1977 / 64 : ℚ) : ℝ) ∧
    heightZ ((1977 / 64 : ℚ) : ℝ) ≤ ((1068052339168849299 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((66753271198053081 / 1152921504606846976 : ℚ) : ℝ) ≤ Real.exp (-((1977 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-203 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((1977 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-203 / 192 : ℚ) : ℝ) ≤ ((1068052339168849299 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1977 : ((4306662657938907 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((1977 / 64 : ℚ) : ℝ) ∧
    logKernel ((1977 / 64 : ℚ) : ℝ) ≤ ((8613325315877819 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1977
  constructor
  · exact (show ((4306662657938907 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((66753271198053081 / 1152921504606846976 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1977 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1068052339168849299 / 18446744073709551616 : ℚ) : ℝ) ≤ ((8613325315877819 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1978 : ((525746861223512067 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((989 / 32 : ℚ) : ℝ) ∧
    heightZ ((989 / 32 : ℚ) : ℝ) ≤ ((1051493722447024137 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((525746861223512067 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((989 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-103 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((989 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-103 / 96 : ℚ) : ℝ) ≤ ((1051493722447024137 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1978 : ((529986755265637 / 4503599627370496 : ℚ) : ℝ) ≤ logKernel ((989 / 32 : ℚ) : ℝ) ∧
    logKernel ((989 / 32 : ℚ) : ℝ) ≤ ((8479788084250197 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1978
  constructor
  · exact (show ((529986755265637 / 4503599627370496 : ℚ) : ℝ) ≤ zKernel ((525746861223512067 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((989 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1051493722447024137 / 18446744073709551616 : ℚ) : ℝ) ≤ ((8479788084250197 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1979 : ((517595911641324543 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((1979 / 64 : ℚ) : ℝ) ∧
    heightZ ((1979 / 64 : ℚ) : ℝ) ≤ ((1035191823282649089 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((517595911641324543 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((1979 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-209 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((1979 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-209 / 192 : ℚ) : ℝ) ≤ ((1035191823282649089 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1979 : ((521770072219077 / 4503599627370496 : ℚ) : ℝ) ≤ logKernel ((1979 / 64 : ℚ) : ℝ) ∧
    logKernel ((1979 / 64 : ℚ) : ℝ) ≤ ((8348321155505237 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1979
  constructor
  · exact (show ((521770072219077 / 4503599627370496 : ℚ) : ℝ) ≤ zKernel ((517595911641324543 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1979 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1035191823282649089 / 18446744073709551616 : ℚ) : ℝ) ≤ ((8348321155505237 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1980 : ((1019142661638900407 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((495 / 16 : ℚ) : ℝ) ∧
    heightZ ((495 / 16 : ℚ) : ℝ) ≤ ((509571330819450205 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((1019142661638900407 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((495 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-53 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((495 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-53 / 48 : ℚ) : ℝ) ≤ ((509571330819450205 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1980 : ((8218892432571775 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((495 / 16 : ℚ) : ℝ) ∧
    logKernel ((495 / 16 : ℚ) : ℝ) ≤ ((2054723108142945 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1980
  constructor
  · exact (show ((8218892432571775 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((1019142661638900407 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((495 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((509571330819450205 / 9223372036854775808 : ℚ) : ℝ) ≤ ((2054723108142945 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1981 : ((62708894948981623 / 1152921504606846976 : ℚ) : ℝ) ≤ heightZ ((1981 / 64 : ℚ) : ℝ) ∧
    heightZ ((1981 / 64 : ℚ) : ℝ) ≤ ((1003342319183705971 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((62708894948981623 / 1152921504606846976 : ℚ) : ℝ) ≤ Real.exp (-((1981 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-215 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((1981 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-215 / 192 : ℚ) : ℝ) ≤ ((1003342319183705971 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1981 : ((4045735157998813 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((1981 / 64 : ℚ) : ℝ) ∧
    logKernel ((1981 / 64 : ℚ) : ℝ) ≤ ((8091470315997631 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1981
  constructor
  · exact (show ((4045735157998813 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((62708894948981623 / 1152921504606846976 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1981 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1003342319183705971 / 18446744073709551616 : ℚ) : ℝ) ≤ ((8091470315997631 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1982 : ((987786938333101757 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((991 / 32 : ℚ) : ℝ) ∧
    heightZ ((991 / 32 : ℚ) : ℝ) ≤ ((15434170911454715 / 288230376151711744 : ℚ) : ℝ) := by
  have h : ((987786938333101757 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((991 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-109 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((991 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-109 / 96 : ℚ) : ℝ) ≤ ((15434170911454715 / 288230376151711744 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1982 : ((7966023696234689 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((991 / 32 : ℚ) : ℝ) ∧
    logKernel ((991 / 32 : ℚ) : ℝ) ≤ ((3983011848117347 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1982
  constructor
  · exact (show ((7966023696234689 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((987786938333101757 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((991 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((15434170911454715 / 288230376151711744 : ℚ) : ℝ) ≤ ((3983011848117347 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1983 : ((121559090163677469 / 2305843009213693952 : ℚ) : ℝ) ≤ heightZ ((1983 / 64 : ℚ) : ℝ) ∧
    heightZ ((1983 / 64 : ℚ) : ℝ) ≤ ((972472721309419755 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((121559090163677469 / 2305843009213693952 : ℚ) : ℝ) ≤ Real.exp (-((1983 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-221 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((1983 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-221 / 192 : ℚ) : ℝ) ≤ ((972472721309419755 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1983 : ((7842521946043705 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1983 / 64 : ℚ) : ℝ) ∧
    logKernel ((1983 / 64 : ℚ) : ℝ) ≤ ((3921260973021855 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1983
  constructor
  · exact (show ((7842521946043705 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((121559090163677469 / 2305843009213693952 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1983 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((972472721309419755 / 18446744073709551616 : ℚ) : ℝ) ≤ ((3921260973021855 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1984 : ((957395929214077247 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((31 / 1 : ℚ) : ℝ) ∧
    heightZ ((31 / 1 : ℚ) : ℝ) ≤ ((478697964607038625 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((957395929214077247 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((31 / 1 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-7 / 6 : ℚ) : ℝ) ∧
      Real.exp (-((31 / 1 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-7 / 6 : ℚ) : ℝ) ≤ ((478697964607038625 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1984 : ((3860467456508375 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((31 / 1 : ℚ) : ℝ) ∧
    logKernel ((31 / 1 : ℚ) : ℝ) ≤ ((7720934913016755 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1984
  constructor
  · exact (show ((3860467456508375 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((957395929214077247 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((31 / 1 : ℚ) : ℝ)) hh).trans
      (show zKernel ((478697964607038625 / 9223372036854775808 : ℚ) : ℝ) ≤ ((7720934913016755 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1985 : ((471276440557370623 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((1985 / 64 : ℚ) : ℝ) ∧
    heightZ ((1985 / 64 : ℚ) : ℝ) ≤ ((942552881114741249 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((471276440557370623 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((1985 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-227 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((1985 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-227 / 192 : ℚ) : ℝ) ≤ ((942552881114741249 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1985 : ((7601232912215653 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1985 / 64 : ℚ) : ℝ) ∧
    logKernel ((1985 / 64 : ℚ) : ℝ) ≤ ((3800616456107829 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1985
  constructor
  · exact (show ((7601232912215653 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((471276440557370623 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1985 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((942552881114741249 / 18446744073709551616 : ℚ) : ℝ) ≤ ((3800616456107829 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1986 : ((927939953146645053 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((993 / 32 : ℚ) : ℝ) ∧
    heightZ ((993 / 32 : ℚ) : ℝ) ≤ ((14499061767916329 / 288230376151711744 : ℚ) : ℝ) := by
  have h : ((927939953146645053 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((993 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-115 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((993 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-115 / 96 : ℚ) : ℝ) ≤ ((14499061767916329 / 288230376151711744 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1986 : ((3741693359462277 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((993 / 32 : ℚ) : ℝ) ∧
    logKernel ((993 / 32 : ℚ) : ℝ) ≤ ((7483386718924559 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1986
  constructor
  · exact (show ((3741693359462277 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((927939953146645053 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((993 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((14499061767916329 / 288230376151711744 : ℚ) : ℝ) ≤ ((7483386718924559 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1987 : ((456776788813918835 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((1987 / 64 : ℚ) : ℝ) ∧
    heightZ ((1987 / 64 : ℚ) : ℝ) ≤ ((913553577627837673 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((456776788813918835 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((1987 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-233 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((1987 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-233 / 192 : ℚ) : ℝ) ≤ ((913553577627837673 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1987 : ((7367367561514817 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1987 / 64 : ℚ) : ℝ) ∧
    logKernel ((1987 / 64 : ℚ) : ℝ) ≤ ((3683683780757411 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1987
  constructor
  · exact (show ((7367367561514817 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((456776788813918835 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1987 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((913553577627837673 / 18446744073709551616 : ℚ) : ℝ) ≤ ((3683683780757411 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1988 : ((449695121094074983 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((497 / 16 : ℚ) : ℝ) ∧
    heightZ ((497 / 16 : ℚ) : ℝ) ≤ ((899390242188149969 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((449695121094074983 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((497 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-59 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((497 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-59 / 48 : ℚ) : ℝ) ≤ ((899390242188149969 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1988 : ((3626573557210281 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((497 / 16 : ℚ) : ℝ) ∧
    logKernel ((497 / 16 : ℚ) : ℝ) ≤ ((7253147114420567 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1988
  constructor
  · exact (show ((3626573557210281 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((449695121094074983 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((497 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((899390242188149969 / 18446744073709551616 : ℚ) : ℝ) ≤ ((7253147114420567 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1989 : ((885446488911664993 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1989 / 64 : ℚ) : ℝ) ∧
    heightZ ((1989 / 64 : ℚ) : ℝ) ≤ ((221361622227916249 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((885446488911664993 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1989 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-239 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((1989 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-239 / 192 : ℚ) : ℝ) ≤ ((221361622227916249 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1989 : ((3570348745611551 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((1989 / 64 : ℚ) : ℝ) ∧
    logKernel ((1989 / 64 : ℚ) : ℝ) ≤ ((7140697491223107 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1989
  constructor
  · exact (show ((3570348745611551 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((885446488911664993 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1989 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((221361622227916249 / 4611686018427387904 : ℚ) : ℝ) ≤ ((7140697491223107 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1990 : ((871718913492483047 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((995 / 32 : ℚ) : ℝ) ∧
    heightZ ((995 / 32 : ℚ) : ℝ) ≤ ((435859456746241525 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((871718913492483047 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((995 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-121 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((995 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-121 / 96 : ℚ) : ℝ) ≤ ((435859456746241525 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1990 : ((7029991237842603 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((995 / 32 : ℚ) : ℝ) ∧
    logKernel ((995 / 32 : ℚ) : ℝ) ≤ ((439374452365163 / 4503599627370496 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1990
  constructor
  · exact (show ((7029991237842603 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((871718913492483047 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((995 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((435859456746241525 / 9223372036854775808 : ℚ) : ℝ) ≤ ((439374452365163 / 4503599627370496 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1991 : ((214551041100893849 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((1991 / 64 : ℚ) : ℝ) ∧
    heightZ ((1991 / 64 : ℚ) : ℝ) ≤ ((858204164403575399 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((214551041100893849 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((1991 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-245 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((1991 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-245 / 192 : ℚ) : ℝ) ≤ ((858204164403575399 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1991 : ((6921001325835283 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1991 / 64 : ℚ) : ℝ) ∧
    logKernel ((1991 / 64 : ℚ) : ℝ) ≤ ((865125165729411 / 9007199254740992 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1991
  constructor
  · exact (show ((6921001325835283 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((214551041100893849 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1991 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((858204164403575399 / 18446744073709551616 : ℚ) : ℝ) ≤ ((865125165729411 / 9007199254740992 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1992 : ((211224735519630931 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((249 / 8 : ℚ) : ℝ) ∧
    heightZ ((249 / 8 : ℚ) : ℝ) ≤ ((844898942078523727 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((211224735519630931 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((249 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-31 / 24 : ℚ) : ℝ) ∧
      Real.exp (-((249 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-31 / 24 : ℚ) : ℝ) ≤ ((844898942078523727 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1992 : ((425856321612159 / 4503599627370496 : ℚ) : ℝ) ≤ logKernel ((249 / 8 : ℚ) : ℝ) ∧
    logKernel ((249 / 8 : ℚ) : ℝ) ≤ ((6813701145794549 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1992
  constructor
  · exact (show ((425856321612159 / 4503599627370496 : ℚ) : ℝ) ≤ zKernel ((211224735519630931 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((249 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((844898942078523727 / 18446744073709551616 : ℚ) : ℝ) ≤ ((6813701145794549 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1993 : ((831799998105945537 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1993 / 64 : ℚ) : ℝ) ∧
    heightZ ((1993 / 64 : ℚ) : ℝ) ≤ ((207949999526486385 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((831799998105945537 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1993 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-251 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((1993 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-251 / 192 : ℚ) : ℝ) ≤ ((207949999526486385 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1993 : ((6708064500854397 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1993 / 64 : ℚ) : ℝ) ∧
    logKernel ((1993 / 64 : ℚ) : ℝ) ≤ ((3354032250427201 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1993
  constructor
  · exact (show ((6708064500854397 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((831799998105945537 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1993 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((207949999526486385 / 4611686018427387904 : ℚ) : ℝ) ≤ ((3354032250427201 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1994 : ((409452067218204421 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((997 / 32 : ℚ) : ℝ) ∧
    heightZ ((997 / 32 : ℚ) : ℝ) ≤ ((818904134436408845 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((409452067218204421 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((997 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-127 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((997 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-127 / 96 : ℚ) : ℝ) ≤ ((818904134436408845 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1994 : ((6604065600293617 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((997 / 32 : ℚ) : ℝ) ∧
    logKernel ((997 / 32 : ℚ) : ℝ) ≤ ((3302032800146811 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1994
  constructor
  · exact (show ((6604065600293617 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((409452067218204421 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((997 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((818904134436408845 / 18446744073709551616 : ℚ) : ℝ) ≤ ((3302032800146811 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1995 : ((403104101300821237 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((1995 / 64 : ℚ) : ℝ) ∧
    heightZ ((1995 / 64 : ℚ) : ℝ) ≤ ((806208202601642477 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((403104101300821237 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((1995 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-257 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((1995 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-257 / 192 : ℚ) : ℝ) ≤ ((806208202601642477 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1995 : ((3250839526619525 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((1995 / 64 : ℚ) : ℝ) ∧
    logKernel ((1995 / 64 : ℚ) : ℝ) ≤ ((6501679053239055 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1995
  constructor
  · exact (show ((3250839526619525 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((403104101300821237 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1995 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((806208202601642477 / 18446744073709551616 : ℚ) : ℝ) ≤ ((6501679053239055 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1996 : ((793709102945851447 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((499 / 16 : ℚ) : ℝ) ∧
    heightZ ((499 / 16 : ℚ) : ℝ) ≤ ((396854551472925725 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((793709102945851447 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((499 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-65 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((499 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-65 / 48 : ℚ) : ℝ) ≤ ((396854551472925725 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1996 : ((6400879862466541 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((499 / 16 : ℚ) : ℝ) ∧
    logKernel ((499 / 16 : ℚ) : ℝ) ≤ ((3200439931233273 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1996
  constructor
  · exact (show ((6400879862466541 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((793709102945851447 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((499 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((396854551472925725 / 9223372036854775808 : ℚ) : ℝ) ≤ ((3200439931233273 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1997 : ((781403783868949655 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1997 / 64 : ℚ) : ℝ) ∧
    heightZ ((1997 / 64 : ℚ) : ℝ) ≤ ((390701891934474829 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((781403783868949655 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1997 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-263 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((1997 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-263 / 192 : ℚ) : ℝ) ≤ ((390701891934474829 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1997 : ((6301643418297979 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1997 / 64 : ℚ) : ℝ) ∧
    logKernel ((1997 / 64 : ℚ) : ℝ) ≤ ((49231589205453 / 562949953421312 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1997
  constructor
  · exact (show ((6301643418297979 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((781403783868949655 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1997 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((390701891934474829 / 9223372036854775808 : ℚ) : ℝ) ≤ ((49231589205453 / 562949953421312 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1998 : ((769289241081525159 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((999 / 32 : ℚ) : ℝ) ∧
    heightZ ((999 / 32 : ℚ) : ℝ) ≤ ((384644620540762581 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((769289241081525159 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((999 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-133 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((999 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-133 / 96 : ℚ) : ℝ) ≤ ((384644620540762581 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1998 : ((3101972746296471 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((999 / 32 : ℚ) : ℝ) ∧
    logKernel ((999 / 32 : ℚ) : ℝ) ≤ ((6203945492592947 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1998
  constructor
  · exact (show ((3101972746296471 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((769289241081525159 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((999 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((384644620540762581 / 9223372036854775808 : ℚ) : ℝ) ≤ ((6203945492592947 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1999 : ((378681258435678087 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((1999 / 64 : ℚ) : ℝ) ∧
    heightZ ((1999 / 64 : ℚ) : ℝ) ≤ ((757362516871356177 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((378681258435678087 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((1999 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-269 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((1999 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-269 / 192 : ℚ) : ℝ) ≤ ((757362516871356177 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1999 : ((6107762232833515 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1999 / 64 : ℚ) : ℝ) ∧
    logKernel ((1999 / 64 : ℚ) : ℝ) ≤ ((381735139552095 / 4503599627370496 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1999
  constructor
  · exact (show ((6107762232833515 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((378681258435678087 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1999 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((757362516871356177 / 18446744073709551616 : ℚ) : ℝ) ≤ ((381735139552095 / 4503599627370496 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2000 : ((745620699381298665 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((125 / 4 : ℚ) : ℝ) ∧
    heightZ ((125 / 4 : ℚ) : ℝ) ≤ ((186405174845324667 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((745620699381298665 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((125 / 4 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-17 / 12 : ℚ) : ℝ) ∧
      Real.exp (-((125 / 4 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-17 / 12 : ℚ) : ℝ) ≤ ((186405174845324667 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2000 : ((6013070156300793 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((125 / 4 : ℚ) : ℝ) ∧
    logKernel ((125 / 4 : ℚ) : ℝ) ≤ ((3006535078150399 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2000
  constructor
  · exact (show ((6013070156300793 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((745620699381298665 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((125 / 4 : ℚ) : ℝ)) hh).trans
      (show zKernel ((186405174845324667 / 4611686018427387904 : ℚ) : ℝ) ≤ ((3006535078150399 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2001 : ((734060921898369259 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2001 / 64 : ℚ) : ℝ) ∧
    heightZ ((2001 / 64 : ℚ) : ℝ) ≤ ((367030460949184631 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((734060921898369259 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2001 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-275 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2001 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-275 / 192 : ℚ) : ℝ) ≤ ((367030460949184631 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2001 : ((5919846144341685 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2001 / 64 : ℚ) : ℝ) ∧
    logKernel ((2001 / 64 : ℚ) : ℝ) ≤ ((2959923072170845 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2001
  constructor
  · exact (show ((5919846144341685 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((734060921898369259 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2001 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((367030460949184631 / 9223372036854775808 : ℚ) : ℝ) ≤ ((2959923072170845 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem log_height_bounds_128 : ((123467291250940683 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((985 / 32 : ℚ) : ℝ) ∧
    Real.log ((985 / 32 : ℚ) : ℝ) ≤ ((246934582501881369 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((123467291250940683 / 36028797018963968 : ℚ) : ℝ) ≤ ((985 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((985 / 32 : ℚ) : ℝ) ≤ Real.exp ((246934582501881369 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_128 : heightPower (128 : Fin 988) ≤ ((72744770803991 / 35184372088832 : ℚ) : ℝ) := by
  have hh := log_height_bounds_128
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_128 : heightFactor (128 : Fin 988) ≤ ((2231297320119583 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_128
  obtain ⟨hpl, hph⟩ := kernel_bounds_1969
  obtain ⟨hcl, hch⟩ := kernel_bounds_1970
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1970
  have h : (((970225 / 512 : ℚ) : ℝ) * (logKernel ((1969 / 64 : ℚ) : ℝ) - logKernel ((985 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((985 / 32 : ℚ) : ℝ) + Real.log ((985 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((2231297320119583 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_129 : ((123485575340152663 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((1971 / 64 : ℚ) : ℝ) ∧
    Real.log ((1971 / 64 : ℚ) : ℝ) ≤ ((246971150680305329 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((123485575340152663 / 36028797018963968 : ℚ) : ℝ) ≤ ((1971 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1971 / 64 : ℚ) : ℝ) ≤ Real.exp ((246971150680305329 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_129 : heightPower (129 : Fin 988) ≤ ((36656191086875 / 17592186044416 : ℚ) : ℝ) := by
  have hh := log_height_bounds_129
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_129 : heightFactor (129 : Fin 988) ≤ ((276348949657151 / 35184372088832 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_129
  obtain ⟨hpl, hph⟩ := kernel_bounds_1970
  obtain ⟨hcl, hch⟩ := kernel_bounds_1971
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1971
  have h : (((3884841 / 2048 : ℚ) : ℝ) * (logKernel ((985 / 32 : ℚ) : ℝ) - logKernel ((1971 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1971 / 64 : ℚ) : ℝ) + Real.log ((1971 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((276348949657151 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_130 : ((247007700310324521 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((493 / 16 : ℚ) : ℝ) ∧
    Real.log ((493 / 16 : ℚ) : ℝ) ≤ ((61751925077581131 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((247007700310324521 / 72057594037927936 : ℚ) : ℝ) ≤ ((493 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((493 / 16 : ℚ) : ℝ) ≤ Real.exp ((61751925077581131 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_130 : heightPower (130 : Fin 988) ≤ ((591039875893367 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_130
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_130 : heightFactor (130 : Fin 988) ≤ ((2190473007257643 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_130
  obtain ⟨hpl, hph⟩ := kernel_bounds_1971
  obtain ⟨hcl, hch⟩ := kernel_bounds_1972
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1972
  have h : (((243049 / 128 : ℚ) : ℝ) * (logKernel ((1971 / 64 : ℚ) : ℝ) - logKernel ((493 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((493 / 16 : ℚ) : ℝ) + Real.log ((493 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((2190473007257643 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_131 : ((247044231410745955 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1973 / 64 : ℚ) : ℝ) ∧
    Real.log ((1973 / 64 : ℚ) : ℝ) ≤ ((123522115705372979 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((247044231410745955 / 72057594037927936 : ℚ) : ℝ) ≤ ((1973 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1973 / 64 : ℚ) : ℝ) ≤ Real.exp ((123522115705372979 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_131 : heightPower (131 : Fin 988) ≤ ((148895155503873 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_131
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_131 : heightFactor (131 : Fin 988) ≤ ((1085169927933685 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_131
  obtain ⟨hpl, hph⟩ := kernel_bounds_1972
  obtain ⟨hcl, hch⟩ := kernel_bounds_1973
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1973
  have h : (((3892729 / 2048 : ℚ) : ℝ) * (logKernel ((493 / 16 : ℚ) : ℝ) - logKernel ((1973 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1973 / 64 : ℚ) : ℝ) + Real.log ((1973 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1085169927933685 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_132 : ((30885093000043505 / 9007199254740992 : ℚ) : ℝ) ≤ Real.log ((987 / 32 : ℚ) : ℝ) ∧
    Real.log ((987 / 32 : ℚ) : ℝ) ≤ ((247080744000348043 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((30885093000043505 / 9007199254740992 : ℚ) : ℝ) ≤ ((987 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((987 / 32 : ℚ) : ℝ) ≤ Real.exp ((247080744000348043 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_132 : heightPower (132 : Fin 988) ≤ ((600121295829729 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_132
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_132 : heightFactor (132 : Fin 988) ≤ ((1075195232016805 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_132
  obtain ⟨hpl, hph⟩ := kernel_bounds_1973
  obtain ⟨hcl, hch⟩ := kernel_bounds_1974
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1974
  have h : (((974169 / 512 : ℚ) : ℝ) * (logKernel ((1973 / 64 : ℚ) : ℝ) - logKernel ((987 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((987 / 32 : ℚ) : ℝ) + Real.log ((987 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1075195232016805 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_133 : ((123558619048940329 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((1975 / 64 : ℚ) : ℝ) ∧
    Real.log ((1975 / 64 : ℚ) : ℝ) ≤ ((247117238097880661 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((123558619048940329 / 36028797018963968 : ℚ) : ℝ) ≤ ((1975 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1975 / 64 : ℚ) : ℝ) ≤ Real.exp ((247117238097880661 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_133 : heightPower (133 : Fin 988) ≤ ((75582737176165 / 35184372088832 : ℚ) : ℝ) := by
  have hh := log_height_bounds_133
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_133 : heightFactor (133 : Fin 988) ≤ ((1065311583884685 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_133
  obtain ⟨hpl, hph⟩ := kernel_bounds_1974
  obtain ⟨hcl, hch⟩ := kernel_bounds_1975
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1975
  have h : (((3900625 / 2048 : ℚ) : ℝ) * (logKernel ((987 / 32 : ℚ) : ℝ) - logKernel ((1975 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1975 / 64 : ℚ) : ℝ) + Real.log ((1975 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1065311583884685 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_134 : ((3861776776907269 / 1125899906842624 : ℚ) : ℝ) ≤ Real.log ((247 / 8 : ℚ) : ℝ) ∧
    Real.log ((247 / 8 : ℚ) : ℝ) ≤ ((247153713722065219 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((3861776776907269 / 1125899906842624 : ℚ) : ℝ) ≤ ((247 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((247 / 8 : ℚ) : ℝ) ≤ Real.exp ((247153713722065219 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_134 : heightPower (134 : Fin 988) ≤ ((609202426827395 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_134
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_134 : heightFactor (134 : Fin 988) ≤ ((2111036318019667 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_134
  obtain ⟨hpl, hph⟩ := kernel_bounds_1975
  obtain ⟨hcl, hch⟩ := kernel_bounds_1976
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1976
  have h : (((61009 / 32 : ℚ) : ℝ) * (logKernel ((1975 / 64 : ℚ) : ℝ) - logKernel ((247 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((247 / 8 : ℚ) : ℝ) + Real.log ((247 / 8 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((2111036318019667 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_135 : ((123595085445797353 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((1977 / 64 : ℚ) : ℝ) ∧
    Real.log ((1977 / 64 : ℚ) : ℝ) ≤ ((247190170891594709 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((123595085445797353 / 36028797018963968 : ℚ) : ℝ) ≤ ((1977 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1977 / 64 : ℚ) : ℝ) ≤ Real.exp ((247190170891594709 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_135 : heightPower (135 : Fin 988) ≤ ((613742884156973 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_135
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_135 : heightFactor (135 : Fin 988) ≤ ((2091628280528933 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_135
  obtain ⟨hpl, hph⟩ := kernel_bounds_1976
  obtain ⟨hcl, hch⟩ := kernel_bounds_1977
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1977
  have h : (((3908529 / 2048 : ℚ) : ℝ) * (logKernel ((247 / 8 : ℚ) : ℝ) - logKernel ((1977 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1977 / 64 : ℚ) : ℝ) + Real.log ((1977 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((2091628280528933 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_136 : ((123613304812566881 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((989 / 32 : ℚ) : ℝ) ∧
    Real.log ((989 / 32 : ℚ) : ℝ) ≤ ((247226609625133765 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((123613304812566881 / 36028797018963968 : ℚ) : ℝ) ≤ ((989 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((989 / 32 : ℚ) : ℝ) ≤ Real.exp ((247226609625133765 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_136 : heightPower (136 : Fin 988) ≤ ((154570817367741 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_136
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_136 : heightFactor (136 : Fin 988) ≤ ((2072397435709577 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_136
  obtain ⟨hpl, hph⟩ := kernel_bounds_1977
  obtain ⟨hcl, hch⟩ := kernel_bounds_1978
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1978
  have h : (((978121 / 512 : ℚ) : ℝ) * (logKernel ((1977 / 64 : ℚ) : ℝ) - logKernel ((989 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((989 / 32 : ℚ) : ℝ) + Real.log ((989 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((2072397435709577 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_137 : ((61815757485329679 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((1979 / 64 : ℚ) : ℝ) ∧
    Real.log ((1979 / 64 : ℚ) : ℝ) ≤ ((247263029941318719 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((61815757485329679 / 18014398509481984 : ℚ) : ℝ) ≤ ((1979 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1979 / 64 : ℚ) : ℝ) ≤ Real.exp ((247263029941318719 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_137 : heightPower (137 : Fin 988) ≤ ((311411791421083 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_137
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_137 : heightFactor (137 : Fin 988) ≤ ((1026671089255851 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_137
  obtain ⟨hpl, hph⟩ := kernel_bounds_1978
  obtain ⟨hcl, hch⟩ := kernel_bounds_1979
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1979
  have h : (((3916441 / 2048 : ℚ) : ℝ) * (logKernel ((989 / 32 : ℚ) : ℝ) - logKernel ((1979 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1979 / 64 : ℚ) : ℝ) + Real.log ((1979 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1026671089255851 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_138 : ((30912428982344707 / 9007199254740992 : ℚ) : ℝ) ≤ Real.log ((495 / 16 : ℚ) : ℝ) ∧
    Real.log ((495 / 16 : ℚ) : ℝ) ≤ ((247299431858757659 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((30912428982344707 / 9007199254740992 : ℚ) : ℝ) ≤ ((495 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((495 / 16 : ℚ) : ℝ) ≤ Real.exp ((247299431858757659 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_138 : heightPower (138 : Fin 988) ≤ ((313681912171633 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_138
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_138 : heightFactor (138 : Fin 988) ≤ ((1017230459146983 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_138
  obtain ⟨hpl, hph⟩ := kernel_bounds_1979
  obtain ⟨hcl, hch⟩ := kernel_bounds_1980
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1980
  have h : (((245025 / 128 : ℚ) : ℝ) * (logKernel ((1979 / 64 : ℚ) : ℝ) - logKernel ((495 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((495 / 16 : ℚ) : ℝ) + Real.log ((495 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1017230459146983 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_139 : ((61833953849007621 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((1981 / 64 : ℚ) : ℝ) ∧
    Real.log ((1981 / 64 : ℚ) : ℝ) ≤ ((247335815396030487 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((61833953849007621 / 18014398509481984 : ℚ) : ℝ) ≤ ((1981 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1981 / 64 : ℚ) : ℝ) ≤ Real.exp ((247335815396030487 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_139 : heightPower (139 : Fin 988) ≤ ((315951997023421 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_139
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_139 : heightFactor (139 : Fin 988) ≤ ((2015752078695577 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_139
  obtain ⟨hpl, hph⟩ := kernel_bounds_1980
  obtain ⟨hcl, hch⟩ := kernel_bounds_1981
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1981
  have h : (((3924361 / 2048 : ℚ) : ℝ) * (logKernel ((495 / 16 : ℚ) : ℝ) - logKernel ((1981 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1981 / 64 : ℚ) : ℝ) + Real.log ((1981 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((2015752078695577 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_140 : ((123686090285844485 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((991 / 32 : ℚ) : ℝ) ∧
    Real.log ((991 / 32 : ℚ) : ℝ) ≤ ((247372180571688973 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((123686090285844485 / 36028797018963968 : ℚ) : ℝ) ≤ ((991 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((991 / 32 : ℚ) : ℝ) ≤ Real.exp ((247372180571688973 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_140 : heightPower (140 : Fin 988) ≤ ((318222046012681 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_140
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_140 : heightFactor (140 : Fin 988) ≤ ((1997214097509407 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_140
  obtain ⟨hpl, hph⟩ := kernel_bounds_1981
  obtain ⟨hcl, hch⟩ := kernel_bounds_1982
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1982
  have h : (((982081 / 512 : ℚ) : ℝ) * (logKernel ((1981 / 64 : ℚ) : ℝ) - logKernel ((991 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((991 / 32 : ℚ) : ℝ) + Real.log ((991 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1997214097509407 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_141 : ((247408527404256813 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1983 / 64 : ℚ) : ℝ) ∧
    Real.log ((1983 / 64 : ℚ) : ℝ) ≤ ((15463032962766051 / 4503599627370496 : ℚ) : ℝ) := by
  have hl : Real.exp ((247408527404256813 / 72057594037927936 : ℚ) : ℝ) ≤ ((1983 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1983 / 64 : ℚ) : ℝ) ≤ Real.exp ((15463032962766051 / 4503599627370496 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_141 : heightPower (141 : Fin 988) ≤ ((40061507396949 / 17592186044416 : ℚ) : ℝ) := by
  have hh := log_height_bounds_141
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_141 : heightFactor (141 : Fin 988) ≤ ((989422713278113 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_141
  obtain ⟨hpl, hph⟩ := kernel_bounds_1982
  obtain ⟨hcl, hch⟩ := kernel_bounds_1983
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1983
  have h : (((3932289 / 2048 : ℚ) : ℝ) * (logKernel ((991 / 32 : ℚ) : ℝ) - logKernel ((1983 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1983 / 64 : ℚ) : ℝ) + Real.log ((1983 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((989422713278113 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_142 : ((247444855912229693 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((31 / 1 : ℚ) : ℝ) ∧
    Real.log ((31 / 1 : ℚ) : ℝ) ≤ ((3866325873628589 / 1125899906842624 : ℚ) : ℝ) := by
  have hl : Real.exp ((247444855912229693 / 72057594037927936 : ℚ) : ℝ) ≤ ((31 / 1 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((31 / 1 : ℚ) : ℝ) ≤ Real.exp ((3866325873628589 / 1125899906842624 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_142 : heightPower (142 : Fin 988) ≤ ((645524073096557 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_142
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_142 : heightFactor (142 : Fin 988) ≤ ((1960644531560037 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_142
  obtain ⟨hpl, hph⟩ := kernel_bounds_1983
  obtain ⟨hcl, hch⟩ := kernel_bounds_1984
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1984
  have h : (((1922 / 1 : ℚ) : ℝ) * (logKernel ((1983 / 64 : ℚ) : ℝ) - logKernel ((31 / 1 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((31 / 1 : ℚ) : ℝ) + Real.log ((31 / 1 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1960644531560037 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_143 : ((247481166114075331 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1985 / 64 : ℚ) : ℝ) ∧
    Real.log ((1985 / 64 : ℚ) : ℝ) ≤ ((123740583057037667 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((247481166114075331 / 72057594037927936 : ℚ) : ℝ) ≤ ((1985 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1985 / 64 : ℚ) : ℝ) ≤ Real.exp ((123740583057037667 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_143 : heightPower (143 : Fin 988) ≤ ((162515989083405 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_143
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_143 : heightFactor (143 : Fin 988) ≤ ((971304946012251 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_143
  obtain ⟨hpl, hph⟩ := kernel_bounds_1984
  obtain ⟨hcl, hch⟩ := kernel_bounds_1985
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1985
  have h : (((3940225 / 2048 : ℚ) : ℝ) * (logKernel ((31 / 1 : ℚ) : ℝ) - logKernel ((1985 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1985 / 64 : ℚ) : ℝ) + Real.log ((1985 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((971304946012251 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_144 : ((247517458028233545 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((993 / 32 : ℚ) : ℝ) ∧
    Real.log ((993 / 32 : ℚ) : ℝ) ≤ ((61879364507058387 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((247517458028233545 / 72057594037927936 : ℚ) : ℝ) ≤ ((993 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((993 / 32 : ℚ) : ℝ) ≤ Real.exp ((61879364507058387 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_144 : heightPower (144 : Fin 988) ≤ ((654603768134405 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_144
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_144 : heightFactor (144 : Fin 988) ≤ ((481185000277615 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_144
  obtain ⟨hpl, hph⟩ := kernel_bounds_1985
  obtain ⟨hcl, hch⟩ := kernel_bounds_1986
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1986
  have h : (((986049 / 512 : ℚ) : ℝ) * (logKernel ((1985 / 64 : ℚ) : ℝ) - logKernel ((993 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((993 / 32 : ℚ) : ℝ) + Real.log ((993 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((481185000277615 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_145 : ((247553731673116305 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1987 / 64 : ℚ) : ℝ) ∧
    Real.log ((1987 / 64 : ℚ) : ℝ) ≤ ((61888432918279077 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((247553731673116305 / 72057594037927936 : ℚ) : ℝ) ≤ ((1987 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1987 / 64 : ℚ) : ℝ) ≤ Real.exp ((61888432918279077 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_145 : heightPower (145 : Fin 988) ≤ ((41196469285677 / 17592186044416 : ℚ) : ℝ) := by
  have hh := log_height_bounds_145
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_145 : heightFactor (145 : Fin 988) ≤ ((953516682757257 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_145
  obtain ⟨hpl, hph⟩ := kernel_bounds_1986
  obtain ⟨hcl, hch⟩ := kernel_bounds_1987
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1987
  have h : (((3948169 / 2048 : ℚ) : ℝ) * (logKernel ((993 / 32 : ℚ) : ℝ) - logKernel ((1987 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1987 / 64 : ℚ) : ℝ) + Real.log ((1987 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((953516682757257 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_146 : ((247589987067107787 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((497 / 16 : ℚ) : ℝ) ∧
    Real.log ((497 / 16 : ℚ) : ℝ) ≤ ((123794993533553895 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((247589987067107787 / 72057594037927936 : ℚ) : ℝ) ≤ ((497 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((497 / 16 : ℚ) : ℝ) ≤ Real.exp ((123794993533553895 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_146 : heightPower (146 : Fin 988) ≤ ((663683177714715 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_146
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_146 : heightFactor (146 : Fin 988) ≤ ((944744252674345 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_146
  obtain ⟨hpl, hph⟩ := kernel_bounds_1987
  obtain ⟨hcl, hch⟩ := kernel_bounds_1988
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1988
  have h : (((247009 / 128 : ℚ) : ℝ) * (logKernel ((1987 / 64 : ℚ) : ℝ) - logKernel ((497 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((497 / 16 : ℚ) : ℝ) + Real.log ((497 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((944744252674345 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_147 : ((247626224228564433 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1989 / 64 : ℚ) : ℝ) ∧
    Real.log ((1989 / 64 : ℚ) : ℝ) ≤ ((61906556057141109 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((247626224228564433 / 72057594037927936 : ℚ) : ℝ) ≤ ((1989 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1989 / 64 : ℚ) : ℝ) ≤ Real.exp ((61906556057141109 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_147 : heightPower (147 : Fin 988) ≤ ((668222775637759 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_147
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_147 : heightFactor (147 : Fin 988) ≤ ((58503248563161 / 8796093022208 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_147
  obtain ⟨hpl, hph⟩ := kernel_bounds_1988
  obtain ⟨hcl, hch⟩ := kernel_bounds_1989
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1989
  have h : (((3956121 / 2048 : ℚ) : ℝ) * (logKernel ((497 / 16 : ℚ) : ℝ) - logKernel ((1989 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1989 / 64 : ℚ) : ℝ) + Real.log ((1989 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((58503248563161 / 8796093022208 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_148 : ((123831221587907503 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((995 / 32 : ℚ) : ℝ) ∧
    Real.log ((995 / 32 : ℚ) : ℝ) ≤ ((247662443175815009 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((123831221587907503 / 36028797018963968 : ℚ) : ℝ) ≤ ((995 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((995 / 32 : ℚ) : ℝ) ≤ Real.exp ((247662443175815009 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_148 : heightPower (148 : Fin 988) ≤ ((672762302411561 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_148
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_148 : heightFactor (148 : Fin 988) ≤ ((1854878258117959 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_148
  obtain ⟨hpl, hph⟩ := kernel_bounds_1989
  obtain ⟨hcl, hch⟩ := kernel_bounds_1990
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1990
  have h : (((990025 / 512 : ℚ) : ℝ) * (logKernel ((1989 / 64 : ℚ) : ℝ) - logKernel ((995 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((995 / 32 : ℚ) : ℝ) + Real.log ((995 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1854878258117959 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_149 : ((61924660981790161 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((1991 / 64 : ℚ) : ℝ) ∧
    Real.log ((1991 / 64 : ℚ) : ℝ) ≤ ((247698643927160647 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((61924660981790161 / 18014398509481984 : ℚ) : ℝ) ≤ ((1991 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1991 / 64 : ℚ) : ℝ) ≤ Real.exp ((247698643927160647 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_149 : heightPower (149 : Fin 988) ≤ ((677301758107609 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_149
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_149 : heightFactor (149 : Fin 988) ≤ ((1837809977285867 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_149
  obtain ⟨hpl, hph⟩ := kernel_bounds_1990
  obtain ⟨hcl, hch⟩ := kernel_bounds_1991
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1991
  have h : (((3964081 / 2048 : ℚ) : ℝ) * (logKernel ((995 / 32 : ℚ) : ℝ) - logKernel ((1991 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1991 / 64 : ℚ) : ℝ) + Real.log ((1991 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1837809977285867 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_150 : ((123867413250437457 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((249 / 8 : ℚ) : ℝ) ∧
    Real.log ((249 / 8 : ℚ) : ℝ) ≤ ((247734826500874917 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((123867413250437457 / 36028797018963968 : ℚ) : ℝ) ≤ ((249 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((249 / 8 : ℚ) : ℝ) ≤ Real.exp ((247734826500874917 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_150 : heightPower (150 : Fin 988) ≤ ((170460285699321 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_150
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_150 : heightFactor (150 : Fin 988) ≤ ((1820897684116163 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_150
  obtain ⟨hpl, hph⟩ := kernel_bounds_1991
  obtain ⟨hcl, hch⟩ := kernel_bounds_1992
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1992
  have h : (((62001 / 32 : ℚ) : ℝ) * (logKernel ((1991 / 64 : ℚ) : ℝ) - logKernel ((249 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((249 / 8 : ℚ) : ℝ) + Real.log ((249 / 8 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1820897684116163 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_151 : ((247770990915203873 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1993 / 64 : ℚ) : ℝ) ∧
    Real.log ((1993 / 64 : ℚ) : ℝ) ≤ ((61942747728800969 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((247770990915203873 / 72057594037927936 : ℚ) : ℝ) ≤ ((1993 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1993 / 64 : ℚ) : ℝ) ≤ Real.exp ((61942747728800969 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_151 : heightPower (151 : Fin 988) ≤ ((686380456551861 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_151
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_151 : heightFactor (151 : Fin 988) ≤ ((225517495503689 / 35184372088832 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_151
  obtain ⟨hpl, hph⟩ := kernel_bounds_1992
  obtain ⟨hcl, hch⟩ := kernel_bounds_1993
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1993
  have h : (((3972049 / 2048 : ℚ) : ℝ) * (logKernel ((249 / 8 : ℚ) : ℝ) - logKernel ((1993 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1993 / 64 : ℚ) : ℝ) + Real.log ((1993 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((225517495503689 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_152 : ((247807137188366117 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((997 / 32 : ℚ) : ℝ) ∧
    Real.log ((997 / 32 : ℚ) : ℝ) ≤ ((30975892148545765 / 9007199254740992 : ℚ) : ℝ) := by
  have hl : Real.exp ((247807137188366117 / 72057594037927936 : ℚ) : ℝ) ≤ ((997 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((997 / 32 : ℚ) : ℝ) ≤ Real.exp ((30975892148545765 / 9007199254740992 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_152 : heightPower (152 : Fin 988) ≤ ((690919699442505 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_152
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_152 : heightFactor (152 : Fin 988) ≤ ((1787535415161823 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_152
  obtain ⟨hpl, hph⟩ := kernel_bounds_1993
  obtain ⟨hcl, hch⟩ := kernel_bounds_1994
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1994
  have h : (((994009 / 512 : ℚ) : ℝ) * (logKernel ((1993 / 64 : ℚ) : ℝ) - logKernel ((997 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((997 / 32 : ℚ) : ℝ) + Real.log ((997 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1787535415161823 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_153 : ((30980408167319105 / 9007199254740992 : ℚ) : ℝ) ≤ Real.log ((1995 / 64 : ℚ) : ℝ) ∧
    Real.log ((1995 / 64 : ℚ) : ℝ) ≤ ((247843265338552843 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((30980408167319105 / 9007199254740992 : ℚ) : ℝ) ≤ ((1995 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1995 / 64 : ℚ) : ℝ) ≤ Real.exp ((247843265338552843 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_153 : heightPower (153 : Fin 988) ≤ ((173864717885069 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_153
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_153 : heightFactor (153 : Fin 988) ≤ ((221385331031389 / 35184372088832 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_153
  obtain ⟨hpl, hph⟩ := kernel_bounds_1994
  obtain ⟨hcl, hch⟩ := kernel_bounds_1995
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1995
  have h : (((3980025 / 2048 : ℚ) : ℝ) * (logKernel ((997 / 32 : ℚ) : ℝ) - logKernel ((1995 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1995 / 64 : ℚ) : ℝ) + Real.log ((1995 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((221385331031389 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_154 : ((247879375383927887 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((499 / 16 : ℚ) : ℝ) ∧
    Real.log ((499 / 16 : ℚ) : ℝ) ≤ ((123939687691963945 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((247879375383927887 / 72057594037927936 : ℚ) : ℝ) ≤ ((499 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((499 / 16 : ℚ) : ℝ) ≤ Real.exp ((123939687691963945 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_154 : heightPower (154 : Fin 988) ≤ ((349998986458063 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_154
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_154 : heightFactor (154 : Fin 988) ≤ ((1754780286525369 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_154
  obtain ⟨hpl, hph⟩ := kernel_bounds_1995
  obtain ⟨hcl, hch⟩ := kernel_bounds_1996
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1996
  have h : (((249001 / 128 : ℚ) : ℝ) * (logKernel ((1995 / 64 : ℚ) : ℝ) - logKernel ((499 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((499 / 16 : ℚ) : ℝ) + Real.log ((499 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1754780286525369 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_155 : ((123957733671313905 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((1997 / 64 : ℚ) : ℝ) ∧
    Real.log ((1997 / 64 : ℚ) : ℝ) ≤ ((247915467342627813 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((123957733671313905 / 36028797018963968 : ℚ) : ℝ) ≤ ((1997 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1997 / 64 : ℚ) : ℝ) ≤ Real.exp ((247915467342627813 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_155 : heightPower (155 : Fin 988) ≤ ((704537003640901 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_155
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_155 : heightFactor (155 : Fin 988) ≤ ((1738626965591401 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_155
  obtain ⟨hpl, hph⟩ := kernel_bounds_1996
  obtain ⟨hcl, hch⟩ := kernel_bounds_1997
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1997
  have h : (((3988009 / 2048 : ℚ) : ℝ) * (logKernel ((499 / 16 : ℚ) : ℝ) - logKernel ((1997 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1997 / 64 : ℚ) : ℝ) + Real.log ((1997 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1738626965591401 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_156 : ((247951541232761921 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((999 / 32 : ℚ) : ℝ) ∧
    Real.log ((999 / 32 : ℚ) : ℝ) ≤ ((61987885308190481 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((247951541232761921 / 72057594037927936 : ℚ) : ℝ) ≤ ((999 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((999 / 32 : ℚ) : ℝ) ≤ Real.exp ((61987885308190481 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_156 : heightPower (156 : Fin 988) ≤ ((354537981892671 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_156
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_156 : heightFactor (156 : Fin 988) ≤ ((861310666662331 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_156
  obtain ⟨hpl, hph⟩ := kernel_bounds_1997
  obtain ⟨hcl, hch⟩ := kernel_bounds_1998
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1998
  have h : (((998001 / 512 : ℚ) : ℝ) * (logKernel ((1997 / 64 : ℚ) : ℝ) - logKernel ((999 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((999 / 32 : ℚ) : ℝ) + Real.log ((999 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((861310666662331 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_157 : ((123993798536206175 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((1999 / 64 : ℚ) : ℝ) ∧
    Real.log ((1999 / 64 : ℚ) : ℝ) ≤ ((247987597072412353 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((123993798536206175 / 36028797018963968 : ℚ) : ℝ) ≤ ((1999 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1999 / 64 : ℚ) : ℝ) ≤ Real.exp ((247987597072412353 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_157 : heightPower (157 : Fin 988) ≤ ((44600928338755 / 17592186044416 : ℚ) : ℝ) := by
  have hh := log_height_bounds_157
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_157 : heightFactor (157 : Fin 988) ≤ ((853381024880019 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_157
  obtain ⟨hpl, hph⟩ := kernel_bounds_1998
  obtain ⟨hcl, hch⟩ := kernel_bounds_1999
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1999
  have h : (((3996001 / 2048 : ℚ) : ℝ) * (logKernel ((999 / 32 : ℚ) : ℝ) - logKernel ((1999 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1999 / 64 : ℚ) : ℝ) + Real.log ((1999 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((853381024880019 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_158 : ((248023634879634095 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((125 / 4 : ℚ) : ℝ) ∧
    Real.log ((125 / 4 : ℚ) : ℝ) ≤ ((124011817439817049 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((248023634879634095 / 72057594037927936 : ℚ) : ℝ) ≤ ((125 / 4 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((125 / 4 : ℚ) : ℝ) ≤ Real.exp ((124011817439817049 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_158 : heightPower (158 : Fin 988) ≤ ((179538418153911 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_158
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_158 : heightFactor (158 : Fin 988) ≤ ((422761946745903 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_158
  obtain ⟨hpl, hph⟩ := kernel_bounds_1999
  obtain ⟨hcl, hch⟩ := kernel_bounds_2000
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2000
  have h : (((15625 / 8 : ℚ) : ℝ) * (logKernel ((1999 / 64 : ℚ) : ℝ) - logKernel ((125 / 4 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((125 / 4 : ℚ) : ℝ) + Real.log ((125 / 4 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((422761946745903 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_159 : ((248059654672455079 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2001 / 64 : ℚ) : ℝ) ∧
    Real.log ((2001 / 64 : ℚ) : ℝ) ≤ ((124029827336227541 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((248059654672455079 / 72057594037927936 : ℚ) : ℝ) ≤ ((2001 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2001 / 64 : ℚ) : ℝ) ≤ Real.exp ((124029827336227541 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_159 : heightPower (159 : Fin 988) ≤ ((722692421442455 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_159
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_159 : heightFactor (159 : Fin 988) ≤ ((418869307256341 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_159
  obtain ⟨hpl, hph⟩ := kernel_bounds_2000
  obtain ⟨hcl, hch⟩ := kernel_bounds_2001
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2001
  have h : (((4004001 / 2048 : ℚ) : ℝ) * (logKernel ((125 / 4 : ℚ) : ℝ) - logKernel ((2001 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2001 / 64 : ℚ) : ℝ) + Real.log ((2001 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((418869307256341 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

end LegendreK6.M2Pilot.Enclosures.Height004
