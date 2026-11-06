import LegendreK6.M2PilotDefinitions
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp

/-! Generated proposals: every bound is checked by Lean, not by trusting Arb. -/
namespace LegendreK6.M2Pilot.Enclosures.Height015
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem height_z_bounds_2321 : ((4946063585851027 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2321 / 64 : ℚ) : ℝ) ∧
    heightZ ((2321 / 64 : ℚ) : ℝ) ≤ ((2473031792925515 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((4946063585851027 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2321 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1235 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2321 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1235 / 192 : ℚ) : ℝ) ≤ ((2473031792925515 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2321 : ((684475577561 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2321 / 64 : ℚ) : ℝ) ∧
    logKernel ((2321 / 64 : ℚ) : ℝ) ≤ ((342237788783 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2321
  constructor
  · exact (show ((684475577561 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((4946063585851027 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2321 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((2473031792925515 / 9223372036854775808 : ℚ) : ℝ) ≤ ((342237788783 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2322 : ((2434690988736265 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((1161 / 32 : ℚ) : ℝ) ∧
    heightZ ((1161 / 32 : ℚ) : ℝ) ≤ ((4869381977472533 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((2434690988736265 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((1161 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-619 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1161 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-619 / 96 : ℚ) : ℝ) ≤ ((4869381977472533 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2322 : ((663416477959 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1161 / 32 : ℚ) : ℝ) ∧
    logKernel ((1161 / 32 : ℚ) : ℝ) ≤ ((165854119491 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2322
  constructor
  · exact (show ((663416477959 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((2434690988736265 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1161 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((4869381977472533 / 18446744073709551616 : ℚ) : ℝ) ≤ ((165854119491 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2323 : ((599236150905007 / 2305843009213693952 : ℚ) : ℝ) ≤ heightZ ((2323 / 64 : ℚ) : ℝ) ∧
    heightZ ((2323 / 64 : ℚ) : ℝ) ≤ ((4793889207240059 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((599236150905007 / 2305843009213693952 : ℚ) : ℝ) ≤ Real.exp (-((2323 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1241 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2323 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1241 / 192 : ℚ) : ℝ) ≤ ((4793889207240059 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2323 : ((643005298737 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2323 / 64 : ℚ) : ℝ) ∧
    logKernel ((2323 / 64 : ℚ) : ℝ) ≤ ((321502649371 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2323
  constructor
  · exact (show ((643005298737 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((599236150905007 / 2305843009213693952 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2323 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((4793889207240059 / 18446744073709551616 : ℚ) : ℝ) ≤ ((321502649371 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2324 : ((4719566843926517 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((581 / 16 : ℚ) : ℝ) ∧
    heightZ ((581 / 16 : ℚ) : ℝ) ≤ ((589945855490815 / 2305843009213693952 : ℚ) : ℝ) := by
  have h : ((4719566843926517 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((581 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-311 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((581 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-311 / 48 : ℚ) : ℝ) ≤ ((589945855490815 / 2305843009213693952 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2324 : ((623222105481 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((581 / 16 : ℚ) : ℝ) ∧
    logKernel ((581 / 16 : ℚ) : ℝ) ≤ ((311611052743 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2324
  constructor
  · exact (show ((623222105481 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((4719566843926517 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((581 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((589945855490815 / 2305843009213693952 : ℚ) : ℝ) ≤ ((311611052743 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2325 : ((1161599185513629 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((2325 / 64 : ℚ) : ℝ) ∧
    heightZ ((2325 / 64 : ℚ) : ℝ) ≤ ((4646396742054519 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((1161599185513629 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((2325 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1247 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2325 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1247 / 192 : ℚ) : ℝ) ≤ ((4646396742054519 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2325 : ((151011894273 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((2325 / 64 : ℚ) : ℝ) ∧
    logKernel ((2325 / 64 : ℚ) : ℝ) ≤ ((604047577097 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2325
  constructor
  · exact (show ((151011894273 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((1161599185513629 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2325 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((4646396742054519 / 18446744073709551616 : ℚ) : ℝ) ≤ ((604047577097 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2326 : ((4574361037466209 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1163 / 32 : ℚ) : ℝ) ∧
    heightZ ((1163 / 32 : ℚ) : ℝ) ≤ ((1143590259366553 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((4574361037466209 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1163 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-625 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1163 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-625 / 96 : ℚ) : ℝ) ≤ ((1143590259366553 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2326 : ((292731493461 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((1163 / 32 : ℚ) : ℝ) ∧
    logKernel ((1163 / 32 : ℚ) : ℝ) ≤ ((585462986927 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2326
  constructor
  · exact (show ((292731493461 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((4574361037466209 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1163 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1143590259366553 / 4611686018427387904 : ℚ) : ℝ) ≤ ((585462986927 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2327 : ((2251721071480923 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2327 / 64 : ℚ) : ℝ) ∧
    heightZ ((2327 / 64 : ℚ) : ℝ) ≤ ((4503442142961849 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((2251721071480923 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2327 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1253 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2327 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1253 / 192 : ℚ) : ℝ) ≤ ((4503442142961849 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2327 : ((567450184481 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2327 / 64 : ℚ) : ℝ) ∧
    logKernel ((2327 / 64 : ℚ) : ℝ) ≤ ((283725092243 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2327
  constructor
  · exact (show ((567450184481 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((2251721071480923 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2327 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((4503442142961849 / 18446744073709551616 : ℚ) : ℝ) ≤ ((283725092243 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2328 : ((2216811372002969 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((291 / 8 : ℚ) : ℝ) ∧
    heightZ ((291 / 8 : ℚ) : ℝ) ≤ ((4433622744005941 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((2216811372002969 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((291 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-157 / 24 : ℚ) : ℝ) ∧
      Real.exp (-((291 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-157 / 24 : ℚ) : ℝ) ≤ ((4433622744005941 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2328 : ((549991577709 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((291 / 8 : ℚ) : ℝ) ∧
    logKernel ((291 / 8 : ℚ) : ℝ) ≤ ((274995788857 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2328
  constructor
  · exact (show ((549991577709 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((2216811372002969 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((291 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((4433622744005941 / 18446744073709551616 : ℚ) : ℝ) ≤ ((274995788857 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2329 : ((1091221448624997 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((2329 / 64 : ℚ) : ℝ) ∧
    heightZ ((2329 / 64 : ℚ) : ℝ) ≤ ((4364885794499991 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((1091221448624997 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((2329 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1259 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2329 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1259 / 192 : ℚ) : ℝ) ≤ ((4364885794499991 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2329 : ((533070115797 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2329 / 64 : ℚ) : ℝ) ∧
    logKernel ((2329 / 64 : ℚ) : ℝ) ≤ ((266535057901 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2329
  constructor
  · exact (show ((533070115797 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((1091221448624997 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2329 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((4364885794499991 / 18446744073709551616 : ℚ) : ℝ) ≤ ((266535057901 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2330 : ((537151814077595 / 2305843009213693952 : ℚ) : ℝ) ≤ heightZ ((1165 / 32 : ℚ) : ℝ) ∧
    heightZ ((1165 / 32 : ℚ) : ℝ) ≤ ((4297214512620763 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((537151814077595 / 2305843009213693952 : ℚ) : ℝ) ≤ Real.exp (-((1165 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-631 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1165 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-631 / 96 : ℚ) : ℝ) ≤ ((4297214512620763 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2330 : ((516669272537 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1165 / 32 : ℚ) : ℝ) ∧
    logKernel ((1165 / 32 : ℚ) : ℝ) ≤ ((258334636271 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2330
  constructor
  · exact (show ((516669272537 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((537151814077595 / 2305843009213693952 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1165 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((4297214512620763 / 18446744073709551616 : ℚ) : ℝ) ≤ ((258334636271 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2331 : ((4230592376723071 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2331 / 64 : ℚ) : ℝ) ∧
    heightZ ((2331 / 64 : ℚ) : ℝ) ≤ ((2115296188361537 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((4230592376723071 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2331 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1265 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2331 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1265 / 192 : ℚ) : ℝ) ≤ ((2115296188361537 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2331 : ((500773030175 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2331 / 64 : ℚ) : ℝ) ∧
    logKernel ((2331 / 64 : ℚ) : ℝ) ≤ ((125193257545 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2331
  constructor
  · exact (show ((500773030175 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((4230592376723071 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2331 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((2115296188361537 / 9223372036854775808 : ℚ) : ℝ) ≤ ((125193257545 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2332 : ((4165003121306105 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((583 / 16 : ℚ) : ℝ) ∧
    heightZ ((583 / 16 : ℚ) : ℝ) ≤ ((1041250780326527 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((4165003121306105 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((583 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-317 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((583 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-317 / 48 : ℚ) : ℝ) ≤ ((1041250780326527 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2332 : ((485365863775 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((583 / 16 : ℚ) : ℝ) ∧
    logKernel ((583 / 16 : ℚ) : ℝ) ≤ ((121341465945 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2332
  constructor
  · exact (show ((485365863775 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((4165003121306105 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((583 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1041250780326527 / 4611686018427387904 : ℚ) : ℝ) ≤ ((121341465945 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2333 : ((2050215366521133 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2333 / 64 : ℚ) : ℝ) ∧
    heightZ ((2333 / 64 : ℚ) : ℝ) ≤ ((4100430733042269 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((2050215366521133 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2333 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1271 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2333 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1271 / 192 : ℚ) : ℝ) ≤ ((4100430733042269 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2333 : ((470432726051 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2333 / 64 : ℚ) : ℝ) ∧
    logKernel ((2333 / 64 : ℚ) : ℝ) ≤ ((58804090757 / 9007199254740992 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2333
  constructor
  · exact (show ((470432726051 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((2050215366521133 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2333 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((4100430733042269 / 18446744073709551616 : ℚ) : ℝ) ≤ ((58804090757 / 9007199254740992 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2334 : ((4036859446867585 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1167 / 32 : ℚ) : ℝ) ∧
    heightZ ((1167 / 32 : ℚ) : ℝ) ≤ ((1009214861716897 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((4036859446867585 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1167 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-637 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1167 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-637 / 96 : ℚ) : ℝ) ≤ ((1009214861716897 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2334 : ((227979516337 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((1167 / 32 : ℚ) : ℝ) ∧
    logKernel ((1167 / 32 : ℚ) : ℝ) ≤ ((455959032679 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2334
  constructor
  · exact (show ((227979516337 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((4036859446867585 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1167 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1009214861716897 / 4611686018427387904 : ℚ) : ℝ) ≤ ((455959032679 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2335 : ((1987136871066381 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2335 / 64 : ℚ) : ℝ) ∧
    heightZ ((2335 / 64 : ℚ) : ℝ) ≤ ((3974273742132765 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((1987136871066381 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2335 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1277 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2335 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1277 / 192 : ℚ) : ℝ) ≤ ((3974273742132765 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2335 : ((441930648027 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2335 / 64 : ℚ) : ℝ) ∧
    logKernel ((2335 / 64 : ℚ) : ℝ) ≤ ((13810332751 / 2251799813685248 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2335
  constructor
  · exact (show ((441930648027 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((1987136871066381 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2335 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((3974273742132765 / 18446744073709551616 : ℚ) : ℝ) ≤ ((13810332751 / 2251799813685248 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2336 : ((3912658338813855 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((73 / 2 : ℚ) : ℝ) ∧
    heightZ ((73 / 2 : ℚ) : ℝ) ≤ ((1956329169406929 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((3912658338813855 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((73 / 2 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-20 / 3 : ℚ) : ℝ) ∧
      Real.exp (-((73 / 2 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-20 / 3 : ℚ) : ℝ) ≤ ((1956329169406929 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2336 : ((214166935701 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((73 / 2 : ℚ) : ℝ) ∧
    logKernel ((73 / 2 : ℚ) : ℝ) ≤ ((428333871407 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2336
  constructor
  · exact (show ((214166935701 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((3912658338813855 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((73 / 2 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1956329169406929 / 9223372036854775808 : ℚ) : ℝ) ≤ ((428333871407 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2337 : ((962999548445435 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((2337 / 64 : ℚ) : ℝ) ∧
    heightZ ((2337 / 64 : ℚ) : ℝ) ≤ ((3851998193781743 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((962999548445435 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((2337 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1283 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2337 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1283 / 192 : ℚ) : ℝ) ≤ ((3851998193781743 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2337 : ((207577711807 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2337 / 64 : ℚ) : ℝ) ∧
    logKernel ((2337 / 64 : ℚ) : ℝ) ≤ ((415155423619 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2337
  constructor
  · exact (show ((207577711807 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((962999548445435 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2337 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((3851998193781743 / 18446744073709551616 : ℚ) : ℝ) ≤ ((415155423619 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2338 : ((237017406070587 / 1152921504606846976 : ℚ) : ℝ) ≤ heightZ ((1169 / 32 : ℚ) : ℝ) ∧
    heightZ ((1169 / 32 : ℚ) : ℝ) ≤ ((3792278497129395 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((237017406070587 / 1152921504606846976 : ℚ) : ℝ) ≤ Real.exp (-((1169 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-643 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1169 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-643 / 96 : ℚ) : ℝ) ≤ ((3792278497129395 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2338 : ((50297804255 / 9007199254740992 : ℚ) : ℝ) ≤ logKernel ((1169 / 32 : ℚ) : ℝ) ∧
    logKernel ((1169 / 32 : ℚ) : ℝ) ≤ ((402382434045 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2338
  constructor
  · exact (show ((50297804255 / 9007199254740992 : ℚ) : ℝ) ≤ zKernel ((237017406070587 / 1152921504606846976 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1169 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((3792278497129395 / 18446744073709551616 : ℚ) : ℝ) ≤ ((402382434045 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2339 : ((3733484668556111 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2339 / 64 : ℚ) : ℝ) ∧
    heightZ ((2339 / 64 : ℚ) : ℝ) ≤ ((1866742334278057 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((3733484668556111 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2339 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1289 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2339 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1289 / 192 : ℚ) : ℝ) ≤ ((1866742334278057 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2339 : ((390002428041 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2339 / 64 : ℚ) : ℝ) ∧
    logKernel ((2339 / 64 : ℚ) : ℝ) ≤ ((195001214023 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2339
  constructor
  · exact (show ((390002428041 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((3733484668556111 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2339 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1866742334278057 / 9223372036854775808 : ℚ) : ℝ) ≤ ((195001214023 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2340 : ((1837801176903905 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((585 / 16 : ℚ) : ℝ) ∧
    heightZ ((585 / 16 : ℚ) : ℝ) ≤ ((3675602353807813 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((1837801176903905 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((585 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-323 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((585 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-323 / 48 : ℚ) : ℝ) ≤ ((3675602353807813 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2340 : ((11812603587 / 2251799813685248 : ℚ) : ℝ) ≤ logKernel ((585 / 16 : ℚ) : ℝ) ∧
    logKernel ((585 / 16 : ℚ) : ℝ) ≤ ((378003314789 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2340
  constructor
  · exact (show ((11812603587 / 2251799813685248 : ℚ) : ℝ) ≤ zKernel ((1837801176903905 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((585 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((3675602353807813 / 18446744073709551616 : ℚ) : ℝ) ≤ ((378003314789 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2341 : ((3618617421172481 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2341 / 64 : ℚ) : ℝ) ∧
    heightZ ((2341 / 64 : ℚ) : ℝ) ≤ ((904654355293121 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((3618617421172481 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2341 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1295 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2341 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1295 / 192 : ℚ) : ℝ) ≤ ((904654355293121 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2341 : ((183186687715 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2341 / 64 : ℚ) : ℝ) ∧
    logKernel ((2341 / 64 : ℚ) : ℝ) ≤ ((366373375435 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2341
  constructor
  · exact (show ((183186687715 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((3618617421172481 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2341 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((904654355293121 / 4611686018427387904 : ℚ) : ℝ) ≤ ((366373375435 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2342 : ((3562515958030007 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1171 / 32 : ℚ) : ℝ) ∧
    heightZ ((1171 / 32 : ℚ) : ℝ) ≤ ((1781257979015005 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((3562515958030007 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1171 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-649 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1171 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-649 / 96 : ℚ) : ℝ) ≤ ((1781257979015005 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2342 : ((177550625847 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((1171 / 32 : ℚ) : ℝ) ∧
    logKernel ((1171 / 32 : ℚ) : ℝ) ≤ ((355101251699 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2342
  constructor
  · exact (show ((177550625847 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((3562515958030007 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1171 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1781257979015005 / 9223372036854775808 : ℚ) : ℝ) ≤ ((355101251699 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2343 : ((3507284267455451 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2343 / 64 : ℚ) : ℝ) ∧
    heightZ ((2343 / 64 : ℚ) : ℝ) ≤ ((1753642133727727 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((3507284267455451 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2343 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1301 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2343 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1301 / 192 : ℚ) : ℝ) ≤ ((1753642133727727 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2343 : ((172087967373 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2343 / 64 : ℚ) : ℝ) ∧
    logKernel ((2343 / 64 : ℚ) : ℝ) ≤ ((344175934751 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2343
  constructor
  · exact (show ((172087967373 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((3507284267455451 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2343 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1753642133727727 / 9223372036854775808 : ℚ) : ℝ) ≤ ((344175934751 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2344 : ((3452908864875015 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((293 / 8 : ℚ) : ℝ) ∧
    heightZ ((293 / 8 : ℚ) : ℝ) ≤ ((1726454432437509 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((3452908864875015 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((293 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-163 / 24 : ℚ) : ℝ) ∧
      Real.exp (-((293 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-163 / 24 : ℚ) : ℝ) ≤ ((1726454432437509 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2344 : ((333586754463 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((293 / 8 : ℚ) : ℝ) ∧
    logKernel ((293 / 8 : ℚ) : ℝ) ≤ ((83396688617 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2344
  constructor
  · exact (show ((333586754463 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((3452908864875015 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((293 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1726454432437509 / 9223372036854775808 : ℚ) : ℝ) ≤ ((83396688617 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2345 : ((1699688237386921 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2345 / 64 : ℚ) : ℝ) ∧
    heightZ ((2345 / 64 : ℚ) : ℝ) ≤ ((3399376474773845 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((1699688237386921 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2345 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1307 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2345 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1307 / 192 : ℚ) : ℝ) ≤ ((3399376474773845 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2345 : ((323323369007 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2345 / 64 : ℚ) : ℝ) ∧
    logKernel ((2345 / 64 : ℚ) : ℝ) ≤ ((80830842253 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2345
  constructor
  · exact (show ((323323369007 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((1699688237386921 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2345 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((3399376474773845 / 18446744073709551616 : ℚ) : ℝ) ≤ ((80830842253 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2346 : ((3346674027454853 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1173 / 32 : ℚ) : ℝ) ∧
    heightZ ((1173 / 32 : ℚ) : ℝ) ≤ ((418334253431857 / 2305843009213693952 : ℚ) : ℝ) := by
  have h : ((3346674027454853 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1173 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-655 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1173 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-655 / 96 : ℚ) : ℝ) ≤ ((418334253431857 / 2305843009213693952 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2346 : ((78343938681 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((1173 / 32 : ℚ) : ℝ) ∧
    logKernel ((1173 / 32 : ℚ) : ℝ) ≤ ((313375754729 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2346
  constructor
  · exact (show ((78343938681 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((3346674027454853 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1173 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((418334253431857 / 2305843009213693952 : ℚ) : ℝ) ≤ ((313375754729 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2347 : ((3294788655847843 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2347 / 64 : ℚ) : ℝ) ∧
    heightZ ((2347 / 64 : ℚ) : ℝ) ≤ ((1647394327923923 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((3294788655847843 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2347 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1313 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2347 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1313 / 192 : ℚ) : ℝ) ≤ ((1647394327923923 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2347 : ((303734196357 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2347 / 64 : ℚ) : ℝ) ∧
    logKernel ((2347 / 64 : ℚ) : ℝ) ≤ ((151867098181 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2347
  constructor
  · exact (show ((303734196357 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((3294788655847843 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2347 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1647394327923923 / 9223372036854775808 : ℚ) : ℝ) ≤ ((151867098181 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2348 : ((405463461546005 / 2305843009213693952 : ℚ) : ℝ) ≤ heightZ ((587 / 16 : ℚ) : ℝ) ∧
    heightZ ((587 / 16 : ℚ) : ℝ) ≤ ((3243707692368043 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((405463461546005 / 2305843009213693952 : ℚ) : ℝ) ≤ Real.exp (-((587 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-329 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((587 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-329 / 48 : ℚ) : ℝ) ≤ ((3243707692368043 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2348 : ((294389277557 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((587 / 16 : ℚ) : ℝ) ∧
    logKernel ((587 / 16 : ℚ) : ℝ) ≤ ((147194638781 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2348
  constructor
  · exact (show ((294389277557 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((405463461546005 / 2305843009213693952 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((587 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((3243707692368043 / 18446744073709551616 : ℚ) : ℝ) ≤ ((147194638781 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2349 : ((3193418665823371 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2349 / 64 : ℚ) : ℝ) ∧
    heightZ ((2349 / 64 : ℚ) : ℝ) ≤ ((1596709332911687 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((3193418665823371 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2349 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1319 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2349 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1319 / 192 : ℚ) : ℝ) ≤ ((1596709332911687 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2349 : ((285331871681 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2349 / 64 : ℚ) : ℝ) ∧
    logKernel ((2349 / 64 : ℚ) : ℝ) ≤ ((142665935843 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2349
  constructor
  · exact (show ((285331871681 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((3193418665823371 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2349 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1596709332911687 / 9223372036854775808 : ℚ) : ℝ) ≤ ((142665935843 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2350 : ((1571954649184837 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((1175 / 32 : ℚ) : ℝ) ∧
    heightZ ((1175 / 32 : ℚ) : ℝ) ≤ ((3143909298369677 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((1571954649184837 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((1175 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-661 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1175 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-661 / 96 : ℚ) : ℝ) ≤ ((3143909298369677 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2350 : ((276553132889 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1175 / 32 : ℚ) : ℝ) ∧
    logKernel ((1175 / 32 : ℚ) : ℝ) ≤ ((138276566447 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2350
  constructor
  · exact (show ((276553132889 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((1571954649184837 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1175 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((3143909298369677 / 18446744073709551616 : ℚ) : ℝ) ≤ ((138276566447 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2351 : ((3095167502513117 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2351 / 64 : ℚ) : ℝ) ∧
    heightZ ((2351 / 64 : ℚ) : ℝ) ≤ ((96723984453535 / 576460752303423488 : ℚ) : ℝ) := by
  have h : ((3095167502513117 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2351 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1325 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2351 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1325 / 192 : ℚ) : ℝ) ≤ ((96723984453535 / 576460752303423488 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2351 : ((134022243747 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2351 / 64 : ℚ) : ℝ) ∧
    logKernel ((2351 / 64 : ℚ) : ℝ) ≤ ((268044487499 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2351
  constructor
  · exact (show ((134022243747 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((3095167502513117 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2351 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((96723984453535 / 576460752303423488 : ℚ) : ℝ) ≤ ((268044487499 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2352 : ((761795344539773 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((147 / 4 : ℚ) : ℝ) ∧
    heightZ ((147 / 4 : ℚ) : ℝ) ≤ ((3047181378159095 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((761795344539773 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((147 / 4 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-83 / 12 : ℚ) : ℝ) ∧
      Real.exp (-((147 / 4 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-83 / 12 : ℚ) : ℝ) ≤ ((3047181378159095 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2352 : ((259797625597 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((147 / 4 : ℚ) : ℝ) ∧
    logKernel ((147 / 4 : ℚ) : ℝ) ≤ ((129898812801 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2352
  constructor
  · exact (show ((259797625597 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((761795344539773 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((147 / 4 : ℚ) : ℝ)) hh).trans
      (show zKernel ((3047181378159095 / 18446744073709551616 : ℚ) : ℝ) ≤ ((129898812801 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2353 : ((374992401213357 / 2305843009213693952 : ℚ) : ℝ) ≤ heightZ ((2353 / 64 : ℚ) : ℝ) ∧
    heightZ ((2353 / 64 : ℚ) : ℝ) ≤ ((2999939209706859 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((374992401213357 / 2305843009213693952 : ℚ) : ℝ) ≤ Real.exp (-((2353 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1331 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2353 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1331 / 192 : ℚ) : ℝ) ≤ ((2999939209706859 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2353 : ((251804492967 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2353 / 64 : ℚ) : ℝ) ∧
    logKernel ((2353 / 64 : ℚ) : ℝ) ≤ ((62951123243 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2353
  constructor
  · exact (show ((251804492967 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((374992401213357 / 2305843009213693952 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2353 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((2999939209706859 / 18446744073709551616 : ℚ) : ℝ) ≤ ((62951123243 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem log_height_bounds_480 : ((258780515211216573 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1161 / 32 : ℚ) : ℝ) ∧
    Real.log ((1161 / 32 : ℚ) : ℝ) ≤ ((4043445550175259 / 1125899906842624 : ℚ) : ℝ) := by
  have hl : Real.exp ((258780515211216573 / 72057594037927936 : ℚ) : ℝ) ≤ ((1161 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1161 / 32 : ℚ) : ℝ) ≤ Real.exp ((4043445550175259 / 1125899906842624 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_480 : heightPower (480 : Fin 988) ≤ ((272042964123297 / 35184372088832 : ℚ) : ℝ) := by
  have hh := log_height_bounds_480
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_480 : heightFactor (480 : Fin 988) ≤ ((2850396429515 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_480
  obtain ⟨hpl, hph⟩ := kernel_bounds_2321
  obtain ⟨hcl, hch⟩ := kernel_bounds_2322
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2322
  have h : (((1347921 / 512 : ℚ) : ℝ) * (logKernel ((2321 / 64 : ℚ) : ℝ) - logKernel ((1161 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1161 / 32 : ℚ) : ℝ) + Real.log ((1161 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((2850396429515 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_481 : ((258811541086416213 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2323 / 64 : ℚ) : ℝ) ∧
    Real.log ((2323 / 64 : ℚ) : ℝ) ≤ ((32351442635802027 / 9007199254740992 : ℚ) : ℝ) := by
  have hl : Real.exp ((258811541086416213 / 72057594037927936 : ℚ) : ℝ) ≤ ((2323 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2323 / 64 : ℚ) : ℝ) ≤ Real.exp ((32351442635802027 / 9007199254740992 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_481 : heightPower (481 : Fin 988) ≤ ((2180862954322479 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_481
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_481 : heightFactor (481 : Fin 988) ≤ ((1389958513881 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_481
  obtain ⟨hpl, hph⟩ := kernel_bounds_2322
  obtain ⟨hcl, hch⟩ := kernel_bounds_2323
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2323
  have h : (((5396329 / 2048 : ℚ) : ℝ) * (logKernel ((1161 / 32 : ℚ) : ℝ) - logKernel ((2323 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2323 / 64 : ℚ) : ℝ) + Real.log ((2323 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1389958513881 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_482 : ((258842553608538101 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((581 / 16 : ℚ) : ℝ) ∧
    Real.log ((581 / 16 : ℚ) : ℝ) ≤ ((32355319201067263 / 9007199254740992 : ℚ) : ℝ) := by
  have hl : Real.exp ((258842553608538101 / 72057594037927936 : ℚ) : ℝ) ≤ ((581 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((581 / 16 : ℚ) : ℝ) ≤ Real.exp ((32355319201067263 / 9007199254740992 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_482 : heightPower (482 : Fin 988) ≤ ((2185382143498121 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_482
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_482 : heightFactor (482 : Fin 988) ≤ ((677794784949 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_482
  obtain ⟨hpl, hph⟩ := kernel_bounds_2323
  obtain ⟨hcl, hch⟩ := kernel_bounds_2324
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2324
  have h : (((337561 / 128 : ℚ) : ℝ) * (logKernel ((2323 / 64 : ℚ) : ℝ) - logKernel ((581 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((581 / 16 : ℚ) : ℝ) + Real.log ((581 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((677794784949 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_483 : ((258873552789071225 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2325 / 64 : ℚ) : ℝ) ∧
    Real.log ((2325 / 64 : ℚ) : ℝ) ≤ ((64718388197267807 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((258873552789071225 / 72057594037927936 : ℚ) : ℝ) ≤ ((2325 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2325 / 64 : ℚ) : ℝ) ≤ Real.exp ((64718388197267807 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_483 : heightPower (483 : Fin 988) ≤ ((2189901280558183 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_483
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_483 : heightFactor (483 : Fin 988) ≤ ((165258735225 / 17592186044416 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_483
  obtain ⟨hpl, hph⟩ := kernel_bounds_2324
  obtain ⟨hcl, hch⟩ := kernel_bounds_2325
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2325
  have h : (((5405625 / 2048 : ℚ) : ℝ) * (logKernel ((581 / 16 : ℚ) : ℝ) - logKernel ((2325 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2325 / 64 : ℚ) : ℝ) + Real.log ((2325 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((165258735225 / 17592186044416 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_484 : ((64726134659872439 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((1163 / 32 : ℚ) : ℝ) ∧
    Real.log ((1163 / 32 : ℚ) : ℝ) ≤ ((258904538639489759 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((64726134659872439 / 18014398509481984 : ℚ) : ℝ) ≤ ((1163 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1163 / 32 : ℚ) : ℝ) ≤ Real.exp ((258904538639489759 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_484 : heightPower (484 : Fin 988) ≤ ((548605091386871 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_484
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_484 : heightFactor (484 : Fin 988) ≤ ((2578756958207 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_484
  obtain ⟨hpl, hph⟩ := kernel_bounds_2325
  obtain ⟨hcl, hch⟩ := kernel_bounds_2326
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2326
  have h : (((1352569 / 512 : ℚ) : ℝ) * (logKernel ((2325 / 64 : ℚ) : ℝ) - logKernel ((1163 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1163 / 32 : ℚ) : ℝ) + Real.log ((1163 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((2578756958207 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_485 : ((258935511171253065 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2327 / 64 : ℚ) : ℝ) ∧
    Real.log ((2327 / 64 : ℚ) : ℝ) ≤ ((64733877792813267 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((258935511171253065 / 72057594037927936 : ℚ) : ℝ) ≤ ((2327 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2327 / 64 : ℚ) : ℝ) ≤ Real.exp ((64733877792813267 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_485 : heightPower (485 : Fin 988) ≤ ((2198939398510789 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_485
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_485 : heightFactor (485 : Fin 988) ≤ ((1257494908771 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_485
  obtain ⟨hpl, hph⟩ := kernel_bounds_2326
  obtain ⟨hcl, hch⟩ := kernel_bounds_2327
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2327
  have h : (((5414929 / 2048 : ℚ) : ℝ) * (logKernel ((1163 / 32 : ℚ) : ℝ) - logKernel ((2327 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2327 / 64 : ℚ) : ℝ) + Real.log ((2327 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1257494908771 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_486 : ((258966470395805755 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((291 / 8 : ℚ) : ℝ) ∧
    Real.log ((291 / 8 : ℚ) : ℝ) ≤ ((129483235197902879 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((258966470395805755 / 72057594037927936 : ℚ) : ℝ) ≤ ((291 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((291 / 8 : ℚ) : ℝ) ≤ Real.exp ((129483235197902879 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_486 : heightPower (486 : Fin 988) ≤ ((1101729189746401 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_486
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_486 : heightFactor (486 : Fin 988) ≤ ((2452798444907 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_486
  obtain ⟨hpl, hph⟩ := kernel_bounds_2327
  obtain ⟨hcl, hch⟩ := kernel_bounds_2328
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2328
  have h : (((84681 / 32 : ℚ) : ℝ) * (logKernel ((2327 / 64 : ℚ) : ℝ) - logKernel ((291 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((291 / 8 : ℚ) : ℝ) + Real.log ((291 / 8 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((2452798444907 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_487 : ((258997416324577683 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2329 / 64 : ℚ) : ℝ) ∧
    Real.log ((2329 / 64 : ℚ) : ℝ) ≤ ((129498708162288843 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((258997416324577683 / 72057594037927936 : ℚ) : ℝ) ≤ ((2329 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2329 / 64 : ℚ) : ℝ) ≤ Real.exp ((129498708162288843 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_487 : heightPower (487 : Fin 988) ≤ ((2207977308538171 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_487
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_487 : heightFactor (487 : Fin 988) ≤ ((2392143928085 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_487
  obtain ⟨hpl, hph⟩ := kernel_bounds_2328
  obtain ⟨hcl, hch⟩ := kernel_bounds_2329
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2329
  have h : (((5424241 / 2048 : ℚ) : ℝ) * (logKernel ((291 / 8 : ℚ) : ℝ) - logKernel ((2329 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2329 / 64 : ℚ) : ℝ) + Real.log ((2329 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((2392143928085 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_488 : ((129514174484491993 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((1165 / 32 : ℚ) : ℝ) ∧
    Real.log ((1165 / 32 : ℚ) : ℝ) ≤ ((259028348968983989 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((129514174484491993 / 36028797018963968 : ℚ) : ℝ) ≤ ((1165 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1165 / 32 : ℚ) : ℝ) ≤ Real.exp ((259028348968983989 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_488 : heightPower (488 : Fin 988) ≤ ((2212496185691487 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_488
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_488 : heightFactor (488 : Fin 988) ≤ ((2332988315075 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_488
  obtain ⟨hpl, hph⟩ := kernel_bounds_2329
  obtain ⟨hcl, hch⟩ := kernel_bounds_2330
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2330
  have h : (((1357225 / 512 : ℚ) : ℝ) * (logKernel ((2329 / 64 : ℚ) : ℝ) - logKernel ((1165 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1165 / 32 : ℚ) : ℝ) + Real.log ((1165 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((2332988315075 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_489 : ((64764817085106277 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((2331 / 64 : ℚ) : ℝ) ∧
    Real.log ((2331 / 64 : ℚ) : ℝ) ≤ ((259059268340425111 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((64764817085106277 / 18014398509481984 : ℚ) : ℝ) ≤ ((2331 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2331 / 64 : ℚ) : ℝ) ≤ Real.exp ((259059268340425111 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_489 : heightPower (489 : Fin 988) ≤ ((2217015010997283 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_489
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_489 : heightFactor (489 : Fin 988) ≤ ((284411823801 / 35184372088832 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_489
  obtain ⟨hpl, hph⟩ := kernel_bounds_2330
  obtain ⟨hcl, hch⟩ := kernel_bounds_2331
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2331
  have h : (((5433561 / 2048 : ℚ) : ℝ) * (logKernel ((1165 / 32 : ℚ) : ℝ) - logKernel ((2331 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2331 / 64 : ℚ) : ℝ) + Real.log ((2331 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((284411823801 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_490 : ((259090174450286821 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((583 / 16 : ℚ) : ℝ) ∧
    Real.log ((583 / 16 : ℚ) : ℝ) ≤ ((32386271806285853 / 9007199254740992 : ℚ) : ℝ) := by
  have hl : Real.exp ((259090174450286821 / 72057594037927936 : ℚ) : ℝ) ≤ ((583 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((583 / 16 : ℚ) : ℝ) ≤ Real.exp ((32386271806285853 / 9007199254740992 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_490 : heightPower (490 : Fin 988) ≤ ((1110766892250017 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_490
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_490 : heightFactor (490 : Fin 988) ≤ ((2219026652059 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_490
  obtain ⟨hpl, hph⟩ := kernel_bounds_2331
  obtain ⟨hcl, hch⟩ := kernel_bounds_2332
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2332
  have h : (((339889 / 128 : ℚ) : ℝ) * (logKernel ((2331 / 64 : ℚ) : ℝ) - logKernel ((583 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((583 / 16 : ℚ) : ℝ) + Real.log ((583 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((2219026652059 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_491 : ((259121067309940257 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2333 / 64 : ℚ) : ℝ) ∧
    Real.log ((2333 / 64 : ℚ) : ℝ) ≤ ((64780266827485065 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((259121067309940257 / 72057594037927936 : ℚ) : ℝ) ≤ ((2333 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2333 / 64 : ℚ) : ℝ) ≤ Real.exp ((64780266827485065 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_491 : heightPower (491 : Fin 988) ≤ ((34782070410065 / 4398046511104 : ℚ) : ℝ) := by
  have hh := log_height_bounds_491
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_491 : heightFactor (491 : Fin 988) ≤ ((2164149288915 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_491
  obtain ⟨hpl, hph⟩ := kernel_bounds_2332
  obtain ⟨hcl, hch⟩ := kernel_bounds_2333
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2333
  have h : (((5442889 / 2048 : ℚ) : ℝ) * (logKernel ((583 / 16 : ℚ) : ℝ) - logKernel ((2333 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2333 / 64 : ℚ) : ℝ) + Real.log ((2333 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((2164149288915 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_492 : ((259151946930741925 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1167 / 32 : ℚ) : ℝ) ∧
    Real.log ((1167 / 32 : ℚ) : ℝ) ≤ ((32393993366342741 / 9007199254740992 : ℚ) : ℝ) := by
  have hl : Real.exp ((259151946930741925 / 72057594037927936 : ℚ) : ℝ) ≤ ((1167 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1167 / 32 : ℚ) : ℝ) ≤ Real.exp ((32393993366342741 / 9007199254740992 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_492 : heightPower (492 : Fin 988) ≤ ((557642794068505 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_492
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_492 : heightFactor (492 : Fin 988) ≤ ((1055314079407 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_492
  obtain ⟨hpl, hph⟩ := kernel_bounds_2333
  obtain ⟨hcl, hch⟩ := kernel_bounds_2334
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2334
  have h : (((1361889 / 512 : ℚ) : ℝ) * (logKernel ((2333 / 64 : ℚ) : ℝ) - logKernel ((1167 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1167 / 32 : ℚ) : ℝ) + Real.log ((1167 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1055314079407 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_493 : ((259182813324033743 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2335 / 64 : ℚ) : ℝ) ∧
    Real.log ((2335 / 64 : ℚ) : ℝ) ≤ ((129591406662016873 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((259182813324033743 / 72057594037927936 : ℚ) : ℝ) ≤ ((2335 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2335 / 64 : ℚ) : ℝ) ≤ Real.exp ((129591406662016873 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_493 : heightPower (493 : Fin 988) ≤ ((34923278041155 / 4398046511104 : ℚ) : ℝ) := by
  have hh := log_height_bounds_493
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_493 : heightFactor (493 : Fin 988) ≤ ((257303720889 / 35184372088832 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_493
  obtain ⟨hpl, hph⟩ := kernel_bounds_2334
  obtain ⟨hcl, hch⟩ := kernel_bounds_2335
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2335
  have h : (((5452225 / 2048 : ℚ) : ℝ) * (logKernel ((1167 / 32 : ℚ) : ℝ) - logKernel ((2335 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2335 / 64 : ℚ) : ℝ) + Real.log ((2335 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((257303720889 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_494 : ((129606833250571529 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((73 / 2 : ℚ) : ℝ) ∧
    Real.log ((73 / 2 : ℚ) : ℝ) ≤ ((259213666501143061 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((129606833250571529 / 36028797018963968 : ℚ) : ℝ) ≤ ((73 / 2 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((73 / 2 : ℚ) : ℝ) ≤ Real.exp ((259213666501143061 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_494 : heightPower (494 : Fin 988) ≤ ((559902090342027 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_494
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_494 : heightFactor (494 : Fin 988) ≤ ((250940180723 / 35184372088832 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_494
  obtain ⟨hpl, hph⟩ := kernel_bounds_2335
  obtain ⟨hcl, hch⟩ := kernel_bounds_2336
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2336
  have h : (((5329 / 2 : ℚ) : ℝ) * (logKernel ((2335 / 64 : ℚ) : ℝ) - logKernel ((73 / 2 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((73 / 2 : ℚ) : ℝ) + Real.log ((73 / 2 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((250940180723 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_495 : ((129622253236691337 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2337 / 64 : ℚ) : ℝ) ∧
    Real.log ((2337 / 64 : ℚ) : ℝ) ≤ ((259244506473382677 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((129622253236691337 / 36028797018963968 : ℚ) : ℝ) ≤ ((2337 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2337 / 64 : ℚ) : ℝ) ≤ Real.exp ((259244506473382677 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_495 : heightPower (495 : Fin 988) ≤ ((2244126876520773 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_495
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_495 : heightFactor (495 : Fin 988) ≤ ((122366958315 / 17592186044416 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_495
  obtain ⟨hpl, hph⟩ := kernel_bounds_2336
  obtain ⟨hcl, hch⟩ := kernel_bounds_2337
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2337
  have h : (((5461569 / 2048 : ℚ) : ℝ) * (logKernel ((73 / 2 : ℚ) : ℝ) - logKernel ((2337 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2337 / 64 : ℚ) : ℝ) + Real.log ((2337 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((122366958315 / 17592186044416 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_496 : ((64818833313012719 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((1169 / 32 : ℚ) : ℝ) ∧
    Real.log ((1169 / 32 : ℚ) : ℝ) ≤ ((259275333252050879 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((64818833313012719 / 18014398509481984 : ℚ) : ℝ) ≤ ((1169 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1169 / 32 : ℚ) : ℝ) ≤ Real.exp ((259275333252050879 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_496 : heightPower (496 : Fin 988) ≤ ((2248645340136049 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_496
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_496 : heightFactor (496 : Fin 988) ≤ ((954724176719 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_496
  obtain ⟨hpl, hph⟩ := kernel_bounds_2337
  obtain ⟨hcl, hch⟩ := kernel_bounds_2338
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2338
  have h : (((1366561 / 512 : ℚ) : ℝ) * (logKernel ((2337 / 64 : ℚ) : ℝ) - logKernel ((1169 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1169 / 32 : ℚ) : ℝ) + Real.log ((1169 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((954724176719 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_497 : ((129653073424215727 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2339 / 64 : ℚ) : ℝ) ∧
    Real.log ((2339 / 64 : ℚ) : ℝ) ≤ ((259306146848431457 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((129653073424215727 / 36028797018963968 : ℚ) : ℝ) ≤ ((2339 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2339 / 64 : ℚ) : ℝ) ≤ Real.exp ((259306146848431457 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_497 : heightPower (497 : Fin 988) ≤ ((2253163752258015 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_497
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_497 : heightFactor (497 : Fin 988) ≤ ((931111099249 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_497
  obtain ⟨hpl, hph⟩ := kernel_bounds_2338
  obtain ⟨hcl, hch⟩ := kernel_bounds_2339
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2339
  have h : (((5470921 / 2048 : ℚ) : ℝ) * (logKernel ((1169 / 32 : ℚ) : ℝ) - logKernel ((2339 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2339 / 64 : ℚ) : ℝ) + Real.log ((2339 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((931111099249 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_498 : ((259336947273793729 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((585 / 16 : ℚ) : ℝ) ∧
    Real.log ((585 / 16 : ℚ) : ℝ) ≤ ((64834236818448433 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((259336947273793729 / 72057594037927936 : ℚ) : ℝ) ≤ ((585 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((585 / 16 : ℚ) : ℝ) ≤ Real.exp ((64834236818448433 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_498 : heightPower (498 : Fin 988) ≤ ((1128841056465345 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_498
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_498 : heightFactor (498 : Fin 988) ≤ ((1816163307781 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_498
  obtain ⟨hpl, hph⟩ := kernel_bounds_2339
  obtain ⟨hcl, hch⟩ := kernel_bounds_2340
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2340
  have h : (((342225 / 128 : ℚ) : ℝ) * (logKernel ((2339 / 64 : ℚ) : ℝ) - logKernel ((585 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((585 / 16 : ℚ) : ℝ) + Real.log ((585 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1816163307781 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_499 : ((129683867269696289 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2341 / 64 : ℚ) : ℝ) ∧
    Real.log ((2341 / 64 : ℚ) : ℝ) ≤ ((259367734539392581 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((129683867269696289 / 36028797018963968 : ℚ) : ℝ) ≤ ((2341 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2341 / 64 : ℚ) : ℝ) ≤ Real.exp ((259367734539392581 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_499 : heightPower (499 : Fin 988) ≤ ((282775052774755 / 35184372088832 : ℚ) : ℝ) := by
  have hh := log_height_bounds_499
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_499 : heightFactor (499 : Fin 988) ≤ ((442810712611 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_499
  obtain ⟨hpl, hph⟩ := kernel_bounds_2340
  obtain ⟨hcl, hch⟩ := kernel_bounds_2341
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2341
  have h : (((5480281 / 2048 : ℚ) : ℝ) * (logKernel ((585 / 16 : ℚ) : ℝ) - logKernel ((2341 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2341 / 64 : ℚ) : ℝ) + Real.log ((2341 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((442810712611 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_500 : ((259398508656468457 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1171 / 32 : ℚ) : ℝ) ∧
    Real.log ((1171 / 32 : ℚ) : ℝ) ≤ ((64849627164117115 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((259398508656468457 / 72057594037927936 : ℚ) : ℝ) ≤ ((1171 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1171 / 32 : ℚ) : ℝ) ≤ Real.exp ((64849627164117115 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_500 : heightPower (500 : Fin 988) ≤ ((2266718680103971 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_500
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_500 : heightFactor (500 : Fin 988) ≤ ((1727432707243 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_500
  obtain ⟨hpl, hph⟩ := kernel_bounds_2341
  obtain ⟨hcl, hch⟩ := kernel_bounds_2342
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2342
  have h : (((1371241 / 512 : ℚ) : ℝ) * (logKernel ((2341 / 64 : ℚ) : ℝ) - logKernel ((1171 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1171 / 32 : ℚ) : ℝ) + Real.log ((1171 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1727432707243 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_501 : ((129714634818123713 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2343 / 64 : ℚ) : ℝ) ∧
    Real.log ((2343 / 64 : ℚ) : ℝ) ≤ ((259429269636247429 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((129714634818123713 / 36028797018963968 : ℚ) : ℝ) ≤ ((2343 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2343 / 64 : ℚ) : ℝ) ≤ Real.exp ((259429269636247429 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_501 : heightPower (501 : Fin 988) ≤ ((2271236886692337 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_501
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_501 : heightFactor (501 : Fin 988) ≤ ((842352726493 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_501
  obtain ⟨hpl, hph⟩ := kernel_bounds_2342
  obtain ⟨hcl, hch⟩ := kernel_bounds_2343
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2343
  have h : (((5489649 / 2048 : ℚ) : ℝ) * (logKernel ((1171 / 32 : ℚ) : ℝ) - logKernel ((2343 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2343 / 64 : ℚ) : ℝ) + Real.log ((2343 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((842352726493 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_502 : ((32432502186242647 / 9007199254740992 : ℚ) : ℝ) ≤ Real.log ((293 / 8 : ℚ) : ℝ) ∧
    Real.log ((293 / 8 : ℚ) : ℝ) ≤ ((259460017489941179 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((32432502186242647 / 9007199254740992 : ℚ) : ℝ) ≤ ((293 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((293 / 8 : ℚ) : ℝ) ≤ Real.exp ((259460017489941179 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_502 : heightPower (502 : Fin 988) ≤ ((568938760501733 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_502
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_502 : heightFactor (502 : Fin 988) ≤ ((1643034339411 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_502
  obtain ⟨hpl, hph⟩ := kernel_bounds_2343
  obtain ⟨hcl, hch⟩ := kernel_bounds_2344
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2344
  have h : (((85849 / 32 : ℚ) : ℝ) * (logKernel ((2343 / 64 : ℚ) : ℝ) - logKernel ((293 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((293 / 8 : ℚ) : ℝ) + Real.log ((293 / 8 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1643034339411 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_503 : ((259490752228747049 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2345 / 64 : ℚ) : ℝ) ∧
    Real.log ((2345 / 64 : ℚ) : ℝ) ≤ ((64872688057186763 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((259490752228747049 / 72057594037927936 : ℚ) : ℝ) ≤ ((2345 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2345 / 64 : ℚ) : ℝ) ≤ Real.exp ((64872688057186763 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_503 : heightPower (503 : Fin 988) ≤ ((2280273146091497 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_503
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_503 : heightFactor (503 : Fin 988) ≤ ((801196639245 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_503
  obtain ⟨hpl, hph⟩ := kernel_bounds_2344
  obtain ⟨hcl, hch⟩ := kernel_bounds_2345
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2345
  have h : (((5499025 / 2048 : ℚ) : ℝ) * (logKernel ((293 / 8 : ℚ) : ℝ) - logKernel ((2345 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2345 / 64 : ℚ) : ℝ) + Real.log ((2345 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((801196639245 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_504 : ((259521473863848067 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1173 / 32 : ℚ) : ℝ) ∧
    Real.log ((1173 / 32 : ℚ) : ℝ) ≤ ((129760736931924035 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((259521473863848067 / 72057594037927936 : ℚ) : ℝ) ≤ ((1173 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1173 / 32 : ℚ) : ℝ) ≤ Real.exp ((129760736931924035 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_504 : heightPower (504 : Fin 988) ≤ ((1142395599494857 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_504
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_504 : heightFactor (504 : Fin 988) ≤ ((1562756826149 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_504
  obtain ⟨hpl, hph⟩ := kernel_bounds_2345
  obtain ⟨hcl, hch⟩ := kernel_bounds_2346
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2346
  have h : (((1375929 / 512 : ℚ) : ℝ) * (logKernel ((2345 / 64 : ℚ) : ℝ) - logKernel ((1173 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1173 / 32 : ℚ) : ℝ) + Real.log ((1173 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1562756826149 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_505 : ((129776091203206477 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2347 / 64 : ℚ) : ℝ) ∧
    Real.log ((2347 / 64 : ℚ) : ℝ) ≤ ((259552182406412957 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((129776091203206477 / 36028797018963968 : ℚ) : ℝ) ≤ ((2347 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2347 / 64 : ℚ) : ℝ) ≤ Real.exp ((259552182406412957 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_505 : heightPower (505 : Fin 988) ≤ ((572327300186303 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_505
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_505 : heightFactor (505 : Fin 988) ≤ ((1524100166379 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_505
  obtain ⟨hpl, hph⟩ := kernel_bounds_2346
  obtain ⟨hcl, hch⟩ := kernel_bounds_2347
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2347
  have h : (((5508409 / 2048 : ℚ) : ℝ) * (logKernel ((1173 / 32 : ℚ) : ℝ) - logKernel ((2347 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2347 / 64 : ℚ) : ℝ) + Real.log ((2347 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1524100166379 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_506 : ((259582877867596161 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((587 / 16 : ℚ) : ℝ) ∧
    Real.log ((587 / 16 : ℚ) : ℝ) ≤ ((64895719466899041 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((259582877867596161 / 72057594037927936 : ℚ) : ℝ) ≤ ((587 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((587 / 16 : ℚ) : ℝ) ≤ Real.exp ((64895719466899041 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_506 : heightPower (506 : Fin 988) ≤ ((2293827151401563 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_506
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_506 : heightFactor (506 : Fin 988) ≤ ((1486399095745 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_506
  obtain ⟨hpl, hph⟩ := kernel_bounds_2347
  obtain ⟨hcl, hch⟩ := kernel_bounds_2348
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2348
  have h : (((344569 / 128 : ℚ) : ℝ) * (logKernel ((2347 / 64 : ℚ) : ℝ) - logKernel ((587 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((587 / 16 : ℚ) : ℝ) + Real.log ((587 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1486399095745 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_507 : ((129806780129268945 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2349 / 64 : ℚ) : ℝ) ∧
    Real.log ((2349 / 64 : ℚ) : ℝ) ≤ ((259613560258537893 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((129806780129268945 / 36028797018963968 : ℚ) : ℝ) ≤ ((2349 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2349 / 64 : ℚ) : ℝ) ≤ Real.exp ((259613560258537893 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_507 : heightPower (507 : Fin 988) ≤ ((2298345051002283 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_507
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_507 : heightFactor (507 : Fin 988) ≤ ((1449630008281 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_507
  obtain ⟨hpl, hph⟩ := kernel_bounds_2348
  obtain ⟨hcl, hch⟩ := kernel_bounds_2349
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2349
  have h : (((5517801 / 2048 : ℚ) : ℝ) * (logKernel ((587 / 16 : ℚ) : ℝ) - logKernel ((2349 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2349 / 64 : ℚ) : ℝ) + Real.log ((2349 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1449630008281 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_508 : ((259644229590364119 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1175 / 32 : ℚ) : ℝ) ∧
    Real.log ((1175 / 32 : ℚ) : ℝ) ≤ ((129822114795182061 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((259644229590364119 / 72057594037927936 : ℚ) : ℝ) ≤ ((1175 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1175 / 32 : ℚ) : ℝ) ≤ Real.exp ((129822114795182061 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_508 : heightPower (508 : Fin 988) ≤ ((2302862899590833 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_508
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_508 : heightFactor (508 : Fin 988) ≤ ((1413769880743 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_508
  obtain ⟨hpl, hph⟩ := kernel_bounds_2349
  obtain ⟨hcl, hch⟩ := kernel_bounds_2350
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2350
  have h : (((1380625 / 512 : ℚ) : ℝ) * (logKernel ((2349 / 64 : ℚ) : ℝ) - logKernel ((1175 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1175 / 32 : ℚ) : ℝ) + Real.log ((1175 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1413769880743 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_509 : ((2028710045892083 / 562949953421312 : ℚ) : ℝ) ≤ Real.log ((2351 / 64 : ℚ) : ℝ) ∧
    Real.log ((2351 / 64 : ℚ) : ℝ) ≤ ((259674885874186627 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((2028710045892083 / 562949953421312 : ℚ) : ℝ) ≤ ((2351 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2351 / 64 : ℚ) : ℝ) ≤ Real.exp ((259674885874186627 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_509 : heightPower (509 : Fin 988) ≤ ((2307380697210619 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_509
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_509 : heightFactor (509 : Fin 988) ≤ ((1378796258245 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_509
  obtain ⟨hpl, hph⟩ := kernel_bounds_2350
  obtain ⟨hcl, hch⟩ := kernel_bounds_2351
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2351
  have h : (((5527201 / 2048 : ℚ) : ℝ) * (logKernel ((1175 / 32 : ℚ) : ℝ) - logKernel ((2351 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2351 / 64 : ℚ) : ℝ) + Real.log ((2351 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1378796258245 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_510 : ((259705529121103007 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((147 / 4 : ℚ) : ℝ) ∧
    Real.log ((147 / 4 : ℚ) : ℝ) ≤ ((129852764560551505 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((259705529121103007 / 72057594037927936 : ℚ) : ℝ) ≤ ((147 / 4 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((147 / 4 : ℚ) : ℝ) ≤ Real.exp ((129852764560551505 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_510 : heightPower (510 : Fin 988) ≤ ((1155949221952495 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_510
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_510 : heightFactor (510 : Fin 988) ≤ ((168085905029 / 35184372088832 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_510
  obtain ⟨hpl, hph⟩ := kernel_bounds_2351
  obtain ⟨hcl, hch⟩ := kernel_bounds_2352
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2352
  have h : (((21609 / 8 : ℚ) : ℝ) * (logKernel ((2351 / 64 : ℚ) : ℝ) - logKernel ((147 / 4 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((147 / 4 : ℚ) : ℝ) + Real.log ((147 / 4 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((168085905029 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_511 : ((259736159342196717 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2353 / 64 : ℚ) : ℝ) ∧
    Real.log ((2353 / 64 : ℚ) : ℝ) ≤ ((16233509958887295 / 4503599627370496 : ℚ) : ℝ) := by
  have hl : Real.exp ((259736159342196717 / 72057594037927936 : ℚ) : ℝ) ≤ ((2353 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2353 / 64 : ℚ) : ℝ) ≤ Real.exp ((16233509958887295 / 4503599627370496 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_511 : heightPower (511 : Fin 988) ≤ ((2316416139717241 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_511
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_511 : heightFactor (511 : Fin 988) ≤ ((1311421466805 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_511
  obtain ⟨hpl, hph⟩ := kernel_bounds_2352
  obtain ⟨hcl, hch⟩ := kernel_bounds_2353
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2353
  have h : (((5536609 / 2048 : ℚ) : ℝ) * (logKernel ((147 / 4 : ℚ) : ℝ) - logKernel ((2353 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2353 / 64 : ℚ) : ℝ) + Real.log ((2353 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1311421466805 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

end LegendreK6.M2Pilot.Enclosures.Height015
