import LegendreK6.M2PilotDefinitions
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp

/-! Generated proposals: every bound is checked by Lean, not by trusting Arb. -/
namespace LegendreK6.M2Pilot.Enclosures.Height016
set_option maxRecDepth 100000
set_option maxHeartbeats 0

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

theorem height_z_bounds_2354 : ((2953429463189221 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1177 / 32 : ℚ) : ℝ) ∧
    heightZ ((1177 / 32 : ℚ) : ℝ) ≤ ((369178682898653 / 2305843009213693952 : ℚ) : ℝ) := by
  have h : ((2953429463189221 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1177 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-667 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1177 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-667 / 96 : ℚ) : ℝ) ≤ ((369178682898653 / 2305843009213693952 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2354 : ((122028641587 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((1177 / 32 : ℚ) : ℝ) ∧
    logKernel ((1177 / 32 : ℚ) : ℝ) ≤ ((244057283179 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2354
  constructor
  · exact (show ((122028641587 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((2953429463189221 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1177 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((369178682898653 / 2305843009213693952 : ℚ) : ℝ) ≤ ((244057283179 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2355 : ((363455097932073 / 2305843009213693952 : ℚ) : ℝ) ≤ heightZ ((2355 / 64 : ℚ) : ℝ) ∧
    heightZ ((2355 / 64 : ℚ) : ℝ) ≤ ((2907640783456587 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((363455097932073 / 2305843009213693952 : ℚ) : ℝ) ≤ Real.exp (-((2355 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1337 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2355 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1337 / 192 : ℚ) : ℝ) ≤ ((2907640783456587 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2355 : ((14784276873 / 4503599627370496 : ℚ) : ℝ) ≤ logKernel ((2355 / 64 : ℚ) : ℝ) ∧
    logKernel ((2355 / 64 : ℚ) : ℝ) ≤ ((236548429973 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2355
  constructor
  · exact (show ((14784276873 / 4503599627370496 : ℚ) : ℝ) ≤ zKernel ((363455097932073 / 2305843009213693952 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2355 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((2907640783456587 / 18446744073709551616 : ℚ) : ℝ) ≤ ((236548429973 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2356 : ((2862561991404621 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((589 / 16 : ℚ) : ℝ) ∧
    heightZ ((589 / 16 : ℚ) : ℝ) ≤ ((178910124462789 / 1152921504606846976 : ℚ) : ℝ) := by
  have h : ((2862561991404621 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((589 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-335 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((589 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-335 / 48 : ℚ) : ℝ) ≤ ((178910124462789 / 1152921504606846976 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2356 : ((14329412493 / 4503599627370496 : ℚ) : ℝ) ≤ logKernel ((589 / 16 : ℚ) : ℝ) ∧
    logKernel ((589 / 16 : ℚ) : ℝ) ≤ ((229270599893 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2356
  constructor
  · exact (show ((14329412493 / 4503599627370496 : ℚ) : ℝ) ≤ zKernel ((2862561991404621 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((589 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((178910124462789 / 1152921504606846976 : ℚ) : ℝ) ≤ ((229270599893 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2357 : ((704545520311239 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((2357 / 64 : ℚ) : ℝ) ∧
    heightZ ((2357 / 64 : ℚ) : ℝ) ≤ ((2818182081244959 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((704545520311239 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((2357 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1343 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2357 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1343 / 192 : ℚ) : ℝ) ≤ ((2818182081244959 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2357 : ((55554171275 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((2357 / 64 : ℚ) : ℝ) ∧
    logKernel ((2357 / 64 : ℚ) : ℝ) ≤ ((222216685105 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2357
  constructor
  · exact (show ((55554171275 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((704545520311239 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2357 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((2818182081244959 / 18446744073709551616 : ℚ) : ℝ) ≤ ((222216685105 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2358 : ((2774490217818145 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1179 / 32 : ℚ) : ℝ) ∧
    heightZ ((1179 / 32 : ℚ) : ℝ) ≤ ((693622554454537 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((2774490217818145 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1179 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-673 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1179 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-673 / 96 : ℚ) : ℝ) ≤ ((693622554454537 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2358 : ((107689898227 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((1179 / 32 : ℚ) : ℝ) ∧
    logKernel ((1179 / 32 : ℚ) : ℝ) ≤ ((215379796459 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2358
  constructor
  · exact (show ((107689898227 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((2774490217818145 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1179 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((693622554454537 / 4611686018427387904 : ℚ) : ℝ) ≤ ((215379796459 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2359 : ((2731475733948323 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2359 / 64 : ℚ) : ℝ) ∧
    heightZ ((2359 / 64 : ℚ) : ℝ) ≤ ((1365737866974163 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((2731475733948323 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2359 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1349 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2359 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1349 / 192 : ℚ) : ℝ) ≤ ((1365737866974163 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2359 : ((104376628379 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2359 / 64 : ℚ) : ℝ) ∧
    logKernel ((2359 / 64 : ℚ) : ℝ) ≤ ((208753256763 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2359
  constructor
  · exact (show ((104376628379 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((2731475733948323 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2359 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1365737866974163 / 9223372036854775808 : ℚ) : ℝ) ≤ ((208753256763 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2360 : ((2689128127838857 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((295 / 8 : ℚ) : ℝ) ∧
    heightZ ((295 / 8 : ℚ) : ℝ) ≤ ((672282031959715 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((2689128127838857 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((295 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-169 / 24 : ℚ) : ℝ) ∧
      Real.exp (-((295 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-169 / 24 : ℚ) : ℝ) ≤ ((672282031959715 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2360 : ((202330594255 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((295 / 8 : ℚ) : ℝ) ∧
    logKernel ((295 / 8 : ℚ) : ℝ) ≤ ((50582648565 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2360
  constructor
  · exact (show ((202330594255 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((2689128127838857 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((295 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((672282031959715 / 4611686018427387904 : ℚ) : ℝ) ≤ ((50582648565 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2361 : ((2647437060508379 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2361 / 64 : ℚ) : ℝ) ∧
    heightZ ((2361 / 64 : ℚ) : ℝ) ≤ ((1323718530254191 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((2647437060508379 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2361 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1355 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2361 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1355 / 192 : ℚ) : ℝ) ≤ ((1323718530254191 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2361 : ((196105536303 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2361 / 64 : ℚ) : ℝ) ∧
    logKernel ((2361 / 64 : ℚ) : ℝ) ≤ ((49026384077 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2361
  constructor
  · exact (show ((196105536303 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((2647437060508379 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2361 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1323718530254191 / 9223372036854775808 : ℚ) : ℝ) ≤ ((49026384077 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2362 : ((2606392353266571 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1181 / 32 : ℚ) : ℝ) ∧
    heightZ ((1181 / 32 : ℚ) : ℝ) ≤ ((1303196176633287 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((2606392353266571 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1181 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-679 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1181 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-679 / 96 : ℚ) : ℝ) ≤ ((1303196176633287 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2362 : ((95036001625 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((1181 / 32 : ℚ) : ℝ) ∧
    logKernel ((1181 / 32 : ℚ) : ℝ) ≤ ((190072003255 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2362
  constructor
  · exact (show ((95036001625 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((2606392353266571 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1181 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1303196176633287 / 9223372036854775808 : ℚ) : ℝ) ≤ ((190072003255 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2363 : ((2565983985229081 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2363 / 64 : ℚ) : ℝ) ∧
    heightZ ((2363 / 64 : ℚ) : ℝ) ≤ ((641495996307271 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((2565983985229081 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2363 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1361 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2363 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1361 / 192 : ℚ) : ℝ) ≤ ((641495996307271 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2363 : ((184224102493 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2363 / 64 : ℚ) : ℝ) ∧
    logKernel ((2363 / 64 : ℚ) : ℝ) ≤ ((92112051249 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2363
  constructor
  · exact (show ((184224102493 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((2565983985229081 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2363 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((641495996307271 / 4611686018427387904 : ℚ) : ℝ) ≤ ((92112051249 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2364 : ((2526202090870969 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((591 / 16 : ℚ) : ℝ) ∧
    heightZ ((591 / 16 : ℚ) : ℝ) ≤ ((631550522717743 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((2526202090870969 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((591 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-341 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((591 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-341 / 48 : ℚ) : ℝ) ≤ ((631550522717743 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2364 : ((22319515341 / 9007199254740992 : ℚ) : ℝ) ≤ logKernel ((591 / 16 : ℚ) : ℝ) ∧
    logKernel ((591 / 16 : ℚ) : ℝ) ≤ ((178556122733 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2364
  constructor
  · exact (show ((22319515341 / 9007199254740992 : ℚ) : ℝ) ≤ zKernel ((2526202090870969 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((591 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((631550522717743 / 4611686018427387904 : ℚ) : ℝ) ≤ ((178556122733 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2365 : ((1243518478809041 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2365 / 64 : ℚ) : ℝ) ∧
    heightZ ((2365 / 64 : ℚ) : ℝ) ≤ ((2487036957618085 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((1243518478809041 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2365 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1367 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2365 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1367 / 192 : ℚ) : ℝ) ≤ ((2487036957618085 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2365 : ((173062528367 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2365 / 64 : ℚ) : ℝ) ∧
    logKernel ((2365 / 64 : ℚ) : ℝ) ≤ ((43265632093 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2365
  constructor
  · exact (show ((173062528367 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((1243518478809041 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2365 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((2487036957618085 / 18446744073709551616 : ℚ) : ℝ) ≤ ((43265632093 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2366 : ((612119755868943 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((1183 / 32 : ℚ) : ℝ) ∧
    heightZ ((1183 / 32 : ℚ) : ℝ) ≤ ((2448479023475775 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((612119755868943 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((1183 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-685 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1183 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-685 / 96 : ℚ) : ℝ) ≤ ((2448479023475775 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2366 : ((20967244267 / 9007199254740992 : ℚ) : ℝ) ≤ logKernel ((1183 / 32 : ℚ) : ℝ) ∧
    logKernel ((1183 / 32 : ℚ) : ℝ) ≤ ((167737954141 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2366
  constructor
  · exact (show ((20967244267 / 9007199254740992 : ℚ) : ℝ) ≤ zKernel ((612119755868943 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1183 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((2448479023475775 / 18446744073709551616 : ℚ) : ℝ) ≤ ((167737954141 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2367 : ((602629718673595 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((2367 / 64 : ℚ) : ℝ) ∧
    heightZ ((2367 / 64 : ℚ) : ℝ) ≤ ((2410518874694383 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((602629718673595 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((2367 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1373 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2367 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1373 / 192 : ℚ) : ℝ) ≤ ((2410518874694383 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2367 : ((162577199831 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2367 / 64 : ℚ) : ℝ) ∧
    logKernel ((2367 / 64 : ℚ) : ℝ) ≤ ((40644299959 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2367
  constructor
  · exact (show ((162577199831 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((602629718673595 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2367 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((2410518874694383 / 18446744073709551616 : ℚ) : ℝ) ≤ ((40644299959 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2368 : ((2373147243470903 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((37 / 1 : ℚ) : ℝ) ∧
    heightZ ((37 / 1 : ℚ) : ℝ) ≤ ((1186573621735453 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((2373147243470903 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((37 / 1 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-43 / 6 : ℚ) : ℝ) ∧
      Real.exp (-((37 / 1 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-43 / 6 : ℚ) : ℝ) ≤ ((1186573621735453 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2368 : ((39393806311 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((37 / 1 : ℚ) : ℝ) ∧
    logKernel ((37 / 1 : ℚ) : ℝ) ≤ ((157575225249 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2368
  constructor
  · exact (show ((39393806311 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((2373147243470903 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((37 / 1 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1186573621735453 / 9223372036854775808 : ℚ) : ℝ) ≤ ((157575225249 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2369 : ((2336355005686311 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2369 / 64 : ℚ) : ℝ) ∧
    heightZ ((2369 / 64 : ℚ) : ℝ) ≤ ((1168177502843157 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((2336355005686311 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2369 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1379 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2369 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1379 / 192 : ℚ) : ℝ) ≤ ((1168177502843157 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2369 : ((152727145237 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2369 / 64 : ℚ) : ℝ) ∧
    logKernel ((2369 / 64 : ℚ) : ℝ) ≤ ((76363572621 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2369
  constructor
  · exact (show ((152727145237 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((2336355005686311 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2369 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1168177502843157 / 9223372036854775808 : ℚ) : ℝ) ≤ ((76363572621 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2370 : ((575033294669481 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((1185 / 32 : ℚ) : ℝ) ∧
    heightZ ((1185 / 32 : ℚ) : ℝ) ≤ ((2300133178677927 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((575033294669481 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((1185 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-691 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1185 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-691 / 96 : ℚ) : ℝ) ≤ ((2300133178677927 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2370 : ((74014112485 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((1185 / 32 : ℚ) : ℝ) ∧
    logKernel ((1185 / 32 : ℚ) : ℝ) ≤ ((148028224975 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2370
  constructor
  · exact (show ((74014112485 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((575033294669481 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1185 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((2300133178677927 / 18446744073709551616 : ℚ) : ℝ) ≤ ((148028224975 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2371 : ((566118229761585 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((2371 / 64 : ℚ) : ℝ) ∧
    heightZ ((2371 / 64 : ℚ) : ℝ) ≤ ((2264472919046343 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((566118229761585 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((2371 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1385 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2371 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1385 / 192 : ℚ) : ℝ) ≤ ((2264472919046343 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2371 : ((71736937641 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2371 / 64 : ℚ) : ℝ) ∧
    logKernel ((2371 / 64 : ℚ) : ℝ) ≤ ((143473875287 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2371
  constructor
  · exact (show ((71736937641 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((566118229761585 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2371 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((2264472919046343 / 18446744073709551616 : ℚ) : ℝ) ≤ ((143473875287 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2372 : ((1114682760248179 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((593 / 16 : ℚ) : ℝ) ∧
    heightZ ((593 / 16 : ℚ) : ℝ) ≤ ((2229365520496361 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((1114682760248179 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((593 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-347 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((593 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-347 / 48 : ℚ) : ℝ) ≤ ((2229365520496361 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2372 : ((69529824101 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((593 / 16 : ℚ) : ℝ) ∧
    logKernel ((593 / 16 : ℚ) : ℝ) ≤ ((139059648207 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2372
  constructor
  · exact (show ((69529824101 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((1114682760248179 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((593 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((2229365520496361 / 18446744073709551616 : ℚ) : ℝ) ≤ ((139059648207 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2373 : ((2194802411711373 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2373 / 64 : ℚ) : ℝ) ∧
    heightZ ((2373 / 64 : ℚ) : ℝ) ≤ ((137175150731961 / 1152921504606846976 : ℚ) : ℝ) := by
  have h : ((2194802411711373 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2373 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1391 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2373 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1391 / 192 : ℚ) : ℝ) ≤ ((137175150731961 / 1152921504606846976 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2373 : ((33695308153 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((2373 / 64 : ℚ) : ℝ) ∧
    logKernel ((2373 / 64 : ℚ) : ℝ) ≤ ((134781232617 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2373
  constructor
  · exact (show ((33695308153 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((2194802411711373 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2373 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((137175150731961 / 1152921504606846976 : ℚ) : ℝ) ≤ ((134781232617 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2374 : ((540193788565181 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((1187 / 32 : ℚ) : ℝ) ∧
    heightZ ((1187 / 32 : ℚ) : ℝ) ≤ ((2160775154260727 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((540193788565181 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((1187 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-697 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1187 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-697 / 96 : ℚ) : ℝ) ≤ ((2160775154260727 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2374 : ((130634450031 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1187 / 32 : ℚ) : ℝ) ∧
    logKernel ((1187 / 32 : ℚ) : ℝ) ≤ ((32658612509 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2374
  constructor
  · exact (show ((130634450031 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((540193788565181 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1187 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((2160775154260727 / 18446744073709551616 : ℚ) : ℝ) ≤ ((32658612509 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2375 : ((1063637720269747 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2375 / 64 : ℚ) : ℝ) ∧
    heightZ ((2375 / 64 : ℚ) : ℝ) ≤ ((2127275440539497 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((1063637720269747 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2375 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1397 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2375 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1397 / 192 : ℚ) : ℝ) ≤ ((2127275440539497 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2375 : ((63307625269 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2375 / 64 : ℚ) : ℝ) ∧
    logKernel ((2375 / 64 : ℚ) : ℝ) ≤ ((126615250543 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2375
  constructor
  · exact (show ((63307625269 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((1063637720269747 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2375 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((2127275440539497 / 18446744073709551616 : ℚ) : ℝ) ≤ ((126615250543 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2376 : ((2094295091740243 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((297 / 8 : ℚ) : ℝ) ∧
    heightZ ((297 / 8 : ℚ) : ℝ) ≤ ((1047147545870123 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((2094295091740243 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((297 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-175 / 24 : ℚ) : ℝ) ∧
      Real.exp (-((297 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-175 / 24 : ℚ) : ℝ) ≤ ((1047147545870123 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2376 : ((30679927203 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((297 / 8 : ℚ) : ℝ) ∧
    logKernel ((297 / 8 : ℚ) : ℝ) ≤ ((122719708817 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2376
  constructor
  · exact (show ((30679927203 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((2094295091740243 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((297 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1047147545870123 / 9223372036854775808 : ℚ) : ℝ) ≤ ((122719708817 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2377 : ((257728256982023 / 2305843009213693952 : ℚ) : ℝ) ≤ heightZ ((2377 / 64 : ℚ) : ℝ) ∧
    heightZ ((2377 / 64 : ℚ) : ℝ) ≤ ((2061826055856187 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((257728256982023 / 2305843009213693952 : ℚ) : ℝ) ≤ Real.exp (-((2377 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1403 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2377 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1403 / 192 : ℚ) : ℝ) ≤ ((2061826055856187 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2377 : ((59472010153 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2377 / 64 : ℚ) : ℝ) ∧
    logKernel ((2377 / 64 : ℚ) : ℝ) ≤ ((118944020311 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2377
  constructor
  · exact (show ((59472010153 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((257728256982023 / 2305843009213693952 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2377 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((2061826055856187 / 18446744073709551616 : ℚ) : ℝ) ≤ ((118944020311 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2378 : ((2029860405715327 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1189 / 32 : ℚ) : ℝ) ∧
    heightZ ((1189 / 32 : ℚ) : ℝ) ≤ ((1014930202857665 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((2029860405715327 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1189 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-703 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1189 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-703 / 96 : ℚ) : ℝ) ≤ ((1014930202857665 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2378 : ((115284497523 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1189 / 32 : ℚ) : ℝ) ∧
    logKernel ((1189 / 32 : ℚ) : ℝ) ≤ ((14410562191 / 9007199254740992 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2378
  constructor
  · exact (show ((115284497523 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((2029860405715327 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1189 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1014930202857665 / 9223372036854775808 : ℚ) : ℝ) ≤ ((14410562191 / 9007199254740992 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2379 : ((499597584261273 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((2379 / 64 : ℚ) : ℝ) ∧
    heightZ ((2379 / 64 : ℚ) : ℝ) ≤ ((1998390337045095 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((499597584261273 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((2379 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1409 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2379 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1409 / 192 : ℚ) : ℝ) ≤ ((1998390337045095 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2379 : ((111737566419 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2379 / 64 : ℚ) : ℝ) ∧
    logKernel ((2379 / 64 : ℚ) : ℝ) ≤ ((13967195803 / 9007199254740992 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2379
  constructor
  · exact (show ((111737566419 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((499597584261273 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2379 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1998390337045095 / 18446744073709551616 : ℚ) : ℝ) ≤ ((13967195803 / 9007199254740992 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2380 : ((1967408166566931 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((595 / 16 : ℚ) : ℝ) ∧
    heightZ ((595 / 16 : ℚ) : ℝ) ≤ ((983704083283467 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((1967408166566931 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((595 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-353 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((595 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-353 / 48 : ℚ) : ℝ) ≤ ((983704083283467 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2380 : ((108299762913 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((595 / 16 : ℚ) : ℝ) ∧
    logKernel ((595 / 16 : ℚ) : ℝ) ≤ ((54149881459 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2380
  constructor
  · exact (show ((108299762913 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((1967408166566931 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((595 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((983704083283467 / 9223372036854775808 : ℚ) : ℝ) ≤ ((54149881459 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2381 : ((968453165060243 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2381 / 64 : ℚ) : ℝ) ∧
    heightZ ((2381 / 64 : ℚ) : ℝ) ≤ ((1936906330120489 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((968453165060243 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2381 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1415 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2381 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1415 / 192 : ℚ) : ℝ) ≤ ((1936906330120489 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2381 : ((104967729501 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2381 / 64 : ℚ) : ℝ) ∧
    logKernel ((2381 / 64 : ℚ) : ℝ) ≤ ((52483864753 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2381
  constructor
  · exact (show ((104967729501 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((968453165060243 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2381 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1936906330120489 / 18446744073709551616 : ℚ) : ℝ) ≤ ((52483864753 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2382 : ((238359672602105 / 2305843009213693952 : ℚ) : ℝ) ≤ heightZ ((1191 / 32 : ℚ) : ℝ) ∧
    heightZ ((1191 / 32 : ℚ) : ℝ) ≤ ((1906877380816843 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((238359672602105 / 2305843009213693952 : ℚ) : ℝ) ≤ Real.exp (-((1191 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-709 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1191 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-709 / 96 : ℚ) : ℝ) ≤ ((1906877380816843 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2382 : ((25434552995 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((1191 / 32 : ℚ) : ℝ) ∧
    logKernel ((1191 / 32 : ℚ) : ℝ) ≤ ((101738211985 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2382
  constructor
  · exact (show ((25434552995 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((238359672602105 / 2305843009213693952 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1191 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1906877380816843 / 18446744073709551616 : ℚ) : ℝ) ≤ ((101738211985 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2383 : ((58666062100637 / 576460752303423488 : ℚ) : ℝ) ≤ heightZ ((2383 / 64 : ℚ) : ℝ) ∧
    heightZ ((2383 / 64 : ℚ) : ℝ) ≤ ((1877313987220387 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((58666062100637 / 576460752303423488 : ℚ) : ℝ) ≤ Real.exp (-((2383 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1421 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2383 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1421 / 192 : ℚ) : ℝ) ≤ ((1877313987220387 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2383 : ((98608056267 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2383 / 64 : ℚ) : ℝ) ∧
    logKernel ((2383 / 64 : ℚ) : ℝ) ≤ ((6163003517 / 4503599627370496 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2383
  constructor
  · exact (show ((98608056267 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((58666062100637 / 576460752303423488 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2383 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1877313987220387 / 18446744073709551616 : ℚ) : ℝ) ≤ ((6163003517 / 4503599627370496 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2384 : ((1848208931558885 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((149 / 4 : ℚ) : ℝ) ∧
    heightZ ((149 / 4 : ℚ) : ℝ) ≤ ((231026116444861 / 2305843009213693952 : ℚ) : ℝ) := by
  have h : ((1848208931558885 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((149 / 4 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-89 / 12 : ℚ) : ℝ) ∧
      Real.exp (-((149 / 4 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-89 / 12 : ℚ) : ℝ) ≤ ((231026116444861 / 2305843009213693952 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2384 : ((95574205321 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((149 / 4 : ℚ) : ℝ) ∧
    logKernel ((149 / 4 : ℚ) : ℝ) ≤ ((47787102663 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2384
  constructor
  · exact (show ((95574205321 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((1848208931558885 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((149 / 4 : ℚ) : ℝ)) hh).trans
      (show zKernel ((231026116444861 / 2305843009213693952 : ℚ) : ℝ) ≤ ((47787102663 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

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

theorem log_height_bounds_512 : ((129883388274268537 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((1177 / 32 : ℚ) : ℝ) ∧
    Real.log ((1177 / 32 : ℚ) : ℝ) ≤ ((259766776548537077 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((129883388274268537 / 36028797018963968 : ℚ) : ℝ) ≤ ((1177 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1177 / 32 : ℚ) : ℝ) ≤ Real.exp ((259766776548537077 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_512 : heightPower (512 : Fin 988) ≤ ((580233446172653 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_512
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_512 : heightFactor (512 : Fin 988) ≤ ((319744526347 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_512
  obtain ⟨hpl, hph⟩ := kernel_bounds_2353
  obtain ⟨hcl, hch⟩ := kernel_bounds_2354
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2354
  have h : (((1385329 / 512 : ℚ) : ℝ) * (logKernel ((2353 / 64 : ℚ) : ℝ) - logKernel ((1177 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1177 / 32 : ℚ) : ℝ) + Real.log ((1177 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((319744526347 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_513 : ((259797380751179295 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2355 / 64 : ℚ) : ℝ) ∧
    Real.log ((2355 / 64 : ℚ) : ℝ) ≤ ((129898690375589649 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((259797380751179295 / 72057594037927936 : ℚ) : ℝ) ≤ ((2355 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2355 / 64 : ℚ) : ℝ) ≤ Real.exp ((129898690375589649 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_513 : heightPower (513 : Fin 988) ≤ ((36335177794817 / 4398046511104 : ℚ) : ℝ) := by
  have hh := log_height_bounds_513
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_513 : heightFactor (513 : Fin 988) ≤ ((623668418859 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_513
  obtain ⟨hpl, hph⟩ := kernel_bounds_2354
  obtain ⟨hcl, hch⟩ := kernel_bounds_2355
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2355
  have h : (((5546025 / 2048 : ℚ) : ℝ) * (logKernel ((1177 / 32 : ℚ) : ℝ) - logKernel ((2355 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2355 / 64 : ℚ) : ℝ) + Real.log ((2355 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((623668418859 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_514 : ((64956992990291129 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((589 / 16 : ℚ) : ℝ) ∧
    Real.log ((589 / 16 : ℚ) : ℝ) ≤ ((259827971961164519 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((64956992990291129 / 18014398509481984 : ℚ) : ℝ) ≤ ((589 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((589 / 16 : ℚ) : ℝ) ≤ Real.exp ((259827971961164519 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_514 : heightPower (514 : Fin 988) ≤ ((582492230573349 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_514
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_514 : heightFactor (514 : Fin 988) ≤ ((1216477847155 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_514
  obtain ⟨hpl, hph⟩ := kernel_bounds_2355
  obtain ⟨hcl, hch⟩ := kernel_bounds_2356
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2356
  have h : (((346921 / 128 : ℚ) : ℝ) * (logKernel ((2355 / 64 : ℚ) : ℝ) - logKernel ((589 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((589 / 16 : ℚ) : ℝ) + Real.log ((589 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1216477847155 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_515 : ((259858550189519819 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2357 / 64 : ℚ) : ℝ) ∧
    Real.log ((2357 / 64 : ℚ) : ℝ) ≤ ((129929275094759911 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((259858550189519819 / 72057594037927936 : ℚ) : ℝ) ≤ ((2357 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2357 / 64 : ℚ) : ℝ) ≤ Real.exp ((129929275094759911 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_515 : heightPower (515 : Fin 988) ≤ ((2334486415009013 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_515
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_515 : heightFactor (515 : Fin 988) ≤ ((1186381806307 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_515
  obtain ⟨hpl, hph⟩ := kernel_bounds_2356
  obtain ⟨hcl, hch⟩ := kernel_bounds_2357
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2357
  have h : (((5555449 / 2048 : ℚ) : ℝ) * (logKernel ((589 / 16 : ℚ) : ℝ) - logKernel ((2357 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2357 / 64 : ℚ) : ℝ) + Real.log ((2357 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1186381806307 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_516 : ((259889115447258251 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1179 / 32 : ℚ) : ℝ) ∧
    Real.log ((1179 / 32 : ℚ) : ℝ) ≤ ((129944557723629127 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((259889115447258251 / 72057594037927936 : ℚ) : ℝ) ≤ ((1179 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1179 / 32 : ℚ) : ℝ) ≤ Real.exp ((129944557723629127 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_516 : heightPower (516 : Fin 988) ≤ ((1169501928529079 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_516
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_516 : heightFactor (516 : Fin 988) ≤ ((578514932481 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_516
  obtain ⟨hpl, hph⟩ := kernel_bounds_2357
  obtain ⟨hcl, hch⟩ := kernel_bounds_2358
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2358
  have h : (((1390041 / 512 : ℚ) : ℝ) * (logKernel ((2357 / 64 : ℚ) : ℝ) - logKernel ((1179 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1179 / 32 : ℚ) : ℝ) + Real.log ((1179 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((578514932481 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_517 : ((259919667745378853 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2359 / 64 : ℚ) : ℝ) ∧
    Real.log ((2359 / 64 : ℚ) : ℝ) ≤ ((32489958468172357 / 9007199254740992 : ℚ) : ℝ) := by
  have hl : Real.exp ((259919667745378853 / 72057594037927936 : ℚ) : ℝ) ≤ ((2359 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2359 / 64 : ℚ) : ℝ) ≤ Real.exp ((32489958468172357 / 9007199254740992 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_517 : heightPower (517 : Fin 988) ≤ ((585880312120949 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_517
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_517 : heightFactor (517 : Fin 988) ≤ ((564201819157 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_517
  obtain ⟨hpl, hph⟩ := kernel_bounds_2358
  obtain ⟨hcl, hch⟩ := kernel_bounds_2359
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2359
  have h : (((5564881 / 2048 : ℚ) : ℝ) * (logKernel ((1179 / 32 : ℚ) : ℝ) - logKernel ((2359 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2359 / 64 : ℚ) : ℝ) + Real.log ((2359 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((564201819157 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_518 : ((129975103547433339 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((295 / 8 : ℚ) : ℝ) ∧
    Real.log ((295 / 8 : ℚ) : ℝ) ≤ ((259950207094866681 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((129975103547433339 / 36028797018963968 : ℚ) : ℝ) ≤ ((295 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((295 / 8 : ℚ) : ℝ) ≤ Real.exp ((259950207094866681 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_518 : heightPower (518 : Fin 988) ≤ ((587009647332209 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_518
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_518 : heightFactor (518 : Fin 988) ≤ ((137560649435 / 35184372088832 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_518
  obtain ⟨hpl, hph⟩ := kernel_bounds_2359
  obtain ⟨hcl, hch⟩ := kernel_bounds_2360
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2360
  have h : (((87025 / 32 : ℚ) : ℝ) * (logKernel ((2359 / 64 : ℚ) : ℝ) - logKernel ((295 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((295 / 8 : ℚ) : ℝ) + Real.log ((295 / 8 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((137560649435 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_519 : ((64995183376673205 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((2361 / 64 : ℚ) : ℝ) ∧
    Real.log ((2361 / 64 : ℚ) : ℝ) ≤ ((259980733506692823 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((64995183376673205 / 18014398509481984 : ℚ) : ℝ) ≤ ((2361 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2361 / 64 : ℚ) : ℝ) ≤ Real.exp ((259980733506692823 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_519 : heightPower (519 : Fin 988) ≤ ((294069484954517 / 35184372088832 : ℚ) : ℝ) := by
  have hh := log_height_bounds_519
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_519 : heightFactor (519 : Fin 988) ≤ ((536628524151 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_519
  obtain ⟨hpl, hph⟩ := kernel_bounds_2360
  obtain ⟨hcl, hch⟩ := kernel_bounds_2361
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2361
  have h : (((5574321 / 2048 : ℚ) : ℝ) * (logKernel ((295 / 8 : ℚ) : ℝ) - logKernel ((2361 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2361 / 64 : ℚ) : ℝ) + Real.log ((2361 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((536628524151 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_520 : ((260011246991814437 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1181 / 32 : ℚ) : ℝ) ∧
    Real.log ((1181 / 32 : ℚ) : ℝ) ≤ ((32501405873976805 / 9007199254740992 : ℚ) : ℝ) := by
  have hl : Real.exp ((260011246991814437 / 72057594037927936 : ℚ) : ℝ) ≤ ((1181 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1181 / 32 : ℚ) : ℝ) ≤ Real.exp ((32501405873976805 / 9007199254740992 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_520 : heightPower (520 : Fin 988) ≤ ((2357073119448497 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_520
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_520 : heightFactor (520 : Fin 988) ≤ ((1046702140423 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_520
  obtain ⟨hpl, hph⟩ := kernel_bounds_2361
  obtain ⟨hcl, hch⟩ := kernel_bounds_2362
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2362
  have h : (((1394761 / 512 : ℚ) : ℝ) * (logKernel ((2361 / 64 : ℚ) : ℝ) - logKernel ((1181 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1181 / 32 : ℚ) : ℝ) + Real.log ((1181 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1046702140423 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_521 : ((260041747561174769 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2363 / 64 : ℚ) : ℝ) ∧
    Real.log ((2363 / 64 : ℚ) : ℝ) ≤ ((65010436890293693 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((260041747561174769 / 72057594037927936 : ℚ) : ℝ) ≤ ((2363 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2363 / 64 : ℚ) : ℝ) ≤ Real.exp ((65010436890293693 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_521 : heightPower (521 : Fin 988) ≤ ((295198788601083 / 35184372088832 : ℚ) : ℝ) := by
  have hh := log_height_bounds_521
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_521 : heightFactor (521 : Fin 988) ≤ ((510401918317 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_521
  obtain ⟨hpl, hph⟩ := kernel_bounds_2362
  obtain ⟨hcl, hch⟩ := kernel_bounds_2363
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2363
  have h : (((5583769 / 2048 : ℚ) : ℝ) * (logKernel ((1181 / 32 : ℚ) : ℝ) - logKernel ((2363 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2363 / 64 : ℚ) : ℝ) + Real.log ((2363 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((510401918317 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_522 : ((130036117612851585 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((591 / 16 : ℚ) : ℝ) ∧
    Real.log ((591 / 16 : ℚ) : ℝ) ≤ ((260072235225703173 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((130036117612851585 / 36028797018963968 : ℚ) : ℝ) ≤ ((591 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((591 / 16 : ℚ) : ℝ) ≤ Real.exp ((260072235225703173 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_522 : heightPower (522 : Fin 988) ≤ ((2366107447759333 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_522
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_522 : heightFactor (522 : Fin 988) ≤ ((995545912481 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_522
  obtain ⟨hpl, hph⟩ := kernel_bounds_2363
  obtain ⟨hcl, hch⟩ := kernel_bounds_2364
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2364
  have h : (((349281 / 128 : ℚ) : ℝ) * (logKernel ((2363 / 64 : ℚ) : ℝ) - logKernel ((591 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((591 / 16 : ℚ) : ℝ) + Real.log ((591 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((995545912481 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_523 : ((260102709996315125 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2365 / 64 : ℚ) : ℝ) ∧
    Real.log ((2365 / 64 : ℚ) : ℝ) ≤ ((32512838749539391 / 9007199254740992 : ℚ) : ℝ) := by
  have hl : Real.exp ((260102709996315125 / 72057594037927936 : ℚ) : ℝ) ≤ ((2365 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2365 / 64 : ℚ) : ℝ) ≤ Real.exp ((32512838749539391 / 9007199254740992 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_523 : heightPower (523 : Fin 988) ≤ ((2370624536343139 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_523
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_523 : heightFactor (523 : Fin 988) ≤ ((970912544131 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_523
  obtain ⟨hpl, hph⟩ := kernel_bounds_2364
  obtain ⟨hcl, hch⟩ := kernel_bounds_2365
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2365
  have h : (((5593225 / 2048 : ℚ) : ℝ) * (logKernel ((591 / 16 : ℚ) : ℝ) - logKernel ((2365 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2365 / 64 : ℚ) : ℝ) + Real.log ((2365 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((970912544131 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_524 : ((260133171883912275 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1183 / 32 : ℚ) : ℝ) ∧
    Real.log ((1183 / 32 : ℚ) : ℝ) ≤ ((130066585941956139 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((260133171883912275 / 72057594037927936 : ℚ) : ℝ) ≤ ((1183 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1183 / 32 : ℚ) : ℝ) ≤ Real.exp ((130066585941956139 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_524 : heightPower (524 : Fin 988) ≤ ((1187570787301335 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_524
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_524 : heightFactor (524 : Fin 988) ≤ ((946888298487 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_524
  obtain ⟨hpl, hph⟩ := kernel_bounds_2365
  obtain ⟨hcl, hch⟩ := kernel_bounds_2366
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2366
  have h : (((1399489 / 512 : ℚ) : ℝ) * (logKernel ((2365 / 64 : ℚ) : ℝ) - logKernel ((1183 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1183 / 32 : ℚ) : ℝ) + Real.log ((1183 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((946888298487 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_525 : ((260163620899382443 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2367 / 64 : ℚ) : ℝ) ∧
    Real.log ((2367 / 64 : ℚ) : ℝ) ≤ ((130081810449691223 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((260163620899382443 / 72057594037927936 : ℚ) : ℝ) ≤ ((2367 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2367 / 64 : ℚ) : ℝ) ≤ Real.exp ((130081810449691223 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_525 : heightPower (525 : Fin 988) ≤ ((1189829281290227 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_525
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_525 : heightFactor (525 : Fin 988) ≤ ((923458123549 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_525
  obtain ⟨hpl, hph⟩ := kernel_bounds_2366
  obtain ⟨hcl, hch⟩ := kernel_bounds_2367
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2367
  have h : (((5602689 / 2048 : ℚ) : ℝ) * (logKernel ((1183 / 32 : ℚ) : ℝ) - logKernel ((2367 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2367 / 64 : ℚ) : ℝ) + Real.log ((2367 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((923458123549 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_526 : ((260194057053599653 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((37 / 1 : ℚ) : ℝ) ∧
    Real.log ((37 / 1 : ℚ) : ℝ) ≤ ((32524257131699957 / 9007199254740992 : ℚ) : ℝ) := by
  have hl : Real.exp ((260194057053599653 / 72057594037927936 : ℚ) : ℝ) ≤ ((37 / 1 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((37 / 1 : ℚ) : ℝ) ≤ Real.exp ((32524257131699957 / 9007199254740992 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_526 : heightPower (526 : Fin 988) ≤ ((2384175500318969 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_526
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_526 : heightFactor (526 : Fin 988) ≤ ((900607339003 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_526
  obtain ⟨hpl, hph⟩ := kernel_bounds_2367
  obtain ⟨hcl, hch⟩ := kernel_bounds_2368
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2368
  have h : (((2738 / 1 : ℚ) : ℝ) * (logKernel ((2367 / 64 : ℚ) : ℝ) - logKernel ((37 / 1 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((37 / 1 : ℚ) : ℝ) + Real.log ((37 / 1 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((900607339003 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_527 : ((260224480357424159 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2369 / 64 : ℚ) : ℝ) ∧
    Real.log ((2369 / 64 : ℚ) : ℝ) ≤ ((130112240178712081 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((260224480357424159 / 72057594037927936 : ℚ) : ℝ) ≤ ((2369 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2369 / 64 : ℚ) : ℝ) ≤ Real.exp ((130112240178712081 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_527 : heightPower (527 : Fin 988) ≤ ((1194346193930319 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_527
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_527 : heightFactor (527 : Fin 988) ≤ ((439160813529 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_527
  obtain ⟨hpl, hph⟩ := kernel_bounds_2368
  obtain ⟨hcl, hch⟩ := kernel_bounds_2369
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2369
  have h : (((5612161 / 2048 : ℚ) : ℝ) * (logKernel ((37 / 1 : ℚ) : ℝ) - logKernel ((2369 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2369 / 64 : ℚ) : ℝ) + Real.log ((2369 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((439160813529 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_528 : ((130127445410851231 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((1185 / 32 : ℚ) : ℝ) ∧
    Real.log ((1185 / 32 : ℚ) : ℝ) ≤ ((260254890821702465 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((130127445410851231 / 36028797018963968 : ℚ) : ℝ) ≤ ((1185 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1185 / 32 : ℚ) : ℝ) ≤ Real.exp ((260254890821702465 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_528 : heightPower (528 : Fin 988) ≤ ((2393209225247829 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_528
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_528 : heightFactor (528 : Fin 988) ≤ ((428293511747 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_528
  obtain ⟨hpl, hph⟩ := kernel_bounds_2369
  obtain ⟨hcl, hch⟩ := kernel_bounds_2370
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2370
  have h : (((1404225 / 512 : ℚ) : ℝ) * (logKernel ((2369 / 64 : ℚ) : ℝ) - logKernel ((1185 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1185 / 32 : ℚ) : ℝ) + Real.log ((1185 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((428293511747 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_529 : ((260285288457267337 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2371 / 64 : ℚ) : ℝ) ∧
    Real.log ((2371 / 64 : ℚ) : ℝ) ≤ ((65071322114316835 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((260285288457267337 / 72057594037927936 : ℚ) : ℝ) ≤ ((2371 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2371 / 64 : ℚ) : ℝ) ≤ Real.exp ((65071322114316835 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_529 : heightPower (529 : Fin 988) ≤ ((1198863006261429 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_529
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_529 : heightFactor (529 : Fin 988) ≤ ((835389908939 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_529
  obtain ⟨hpl, hph⟩ := kernel_bounds_2370
  obtain ⟨hcl, hch⟩ := kernel_bounds_2371
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2371
  have h : (((5621641 / 2048 : ℚ) : ℝ) * (logKernel ((1185 / 32 : ℚ) : ℝ) - logKernel ((2371 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2371 / 64 : ℚ) : ℝ) + Real.log ((2371 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((835389908939 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_530 : ((508429049365113 / 140737488355328 : ℚ) : ℝ) ≤ Real.log ((593 / 16 : ℚ) : ℝ) ∧
    Real.log ((593 / 16 : ℚ) : ℝ) ≤ ((260315673274937859 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((508429049365113 / 140737488355328 : ℚ) : ℝ) ≤ ((593 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((593 / 16 : ℚ) : ℝ) ≤ Real.exp ((260315673274937859 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_530 : heightPower (530 : Fin 988) ≤ ((600560687431997 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_530
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_530 : heightFactor (530 : Fin 988) ≤ ((407358500181 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_530
  obtain ⟨hpl, hph⟩ := kernel_bounds_2371
  obtain ⟨hcl, hch⟩ := kernel_bounds_2372
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2372
  have h : (((351649 / 128 : ℚ) : ℝ) * (logKernel ((2371 / 64 : ℚ) : ℝ) - logKernel ((593 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((593 / 16 : ℚ) : ℝ) + Real.log ((593 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((407358500181 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_531 : ((260346045285519409 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2373 / 64 : ℚ) : ℝ) ∧
    Real.log ((2373 / 64 : ℚ) : ℝ) ≤ ((65086511321379853 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((260346045285519409 / 72057594037927936 : ℚ) : ℝ) ≤ ((2373 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2373 / 64 : ℚ) : ℝ) ≤ Real.exp ((65086511321379853 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_531 : heightPower (531 : Fin 988) ≤ ((1203379718452713 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_531
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_531 : heightFactor (531 : Fin 988) ≤ ((397277671383 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_531
  obtain ⟨hpl, hph⟩ := kernel_bounds_2372
  obtain ⟨hcl, hch⟩ := kernel_bounds_2373
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2373
  have h : (((5631129 / 2048 : ℚ) : ℝ) * (logKernel ((593 / 16 : ℚ) : ℝ) - logKernel ((2373 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2373 / 64 : ℚ) : ℝ) + Real.log ((2373 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((397277671383 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_532 : ((260376404499803731 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1187 / 32 : ℚ) : ℝ) ∧
    Real.log ((1187 / 32 : ℚ) : ℝ) ≤ ((130188202249901867 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((260376404499803731 / 72057594037927936 : ℚ) : ℝ) ≤ ((1187 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1187 / 32 : ℚ) : ℝ) ≤ Real.exp ((130188202249901867 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_532 : heightPower (532 : Fin 988) ≤ ((150704754631083 / 17592186044416 : ℚ) : ℝ) := by
  have hh := log_height_bounds_532
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_532 : heightFactor (532 : Fin 988) ≤ ((774892301101 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_532
  obtain ⟨hpl, hph⟩ := kernel_bounds_2373
  obtain ⟨hcl, hch⟩ := kernel_bounds_2374
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2374
  have h : (((1408969 / 512 : ℚ) : ℝ) * (logKernel ((2373 / 64 : ℚ) : ℝ) - logKernel ((1187 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1187 / 32 : ℚ) : ℝ) + Real.log ((1187 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((774892301101 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_533 : ((260406750928568919 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2375 / 64 : ℚ) : ℝ) ∧
    Real.log ((2375 / 64 : ℚ) : ℝ) ≤ ((130203375464284461 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((260406750928568919 / 72057594037927936 : ℚ) : ℝ) ≤ ((2375 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2375 / 64 : ℚ) : ℝ) ≤ Real.exp ((130203375464284461 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_533 : heightPower (533 : Fin 988) ≤ ((603948165336449 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_533
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_533 : heightFactor (533 : Fin 988) ≤ ((94464444045 / 35184372088832 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_533
  obtain ⟨hpl, hph⟩ := kernel_bounds_2374
  obtain ⟨hcl, hch⟩ := kernel_bounds_2375
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2375
  have h : (((5640625 / 2048 : ℚ) : ℝ) * (logKernel ((1187 / 32 : ℚ) : ℝ) - logKernel ((2375 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2375 / 64 : ℚ) : ℝ) + Real.log ((2375 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((94464444045 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_534 : ((260437084582579461 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((297 / 8 : ℚ) : ℝ) ∧
    Real.log ((297 / 8 : ℚ) : ℝ) ≤ ((32554635572822433 / 9007199254740992 : ℚ) : ℝ) := by
  have hl : Real.exp ((260437084582579461 / 72057594037927936 : ℚ) : ℝ) ≤ ((297 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((297 / 8 : ℚ) : ℝ) ≤ Real.exp ((32554635572822433 / 9007199254740992 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_534 : heightPower (534 : Fin 988) ≤ ((2420309198692879 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_534
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_534 : heightFactor (534 : Fin 988) ≤ ((737013077883 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_534
  obtain ⟨hpl, hph⟩ := kernel_bounds_2375
  obtain ⟨hcl, hch⟩ := kernel_bounds_2376
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2376
  have h : (((88209 / 32 : ℚ) : ℝ) * (logKernel ((2375 / 64 : ℚ) : ℝ) - logKernel ((297 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((297 / 8 : ℚ) : ℝ) + Real.log ((297 / 8 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((737013077883 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_535 : ((260467405472586255 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2377 / 64 : ℚ) : ℝ) ∧
    Real.log ((2377 / 64 : ℚ) : ℝ) ≤ ((130233702736293129 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((260467405472586255 / 72057594037927936 : ℚ) : ℝ) ≤ ((2377 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2377 / 64 : ℚ) : ℝ) ≤ Real.exp ((130233702736293129 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_535 : heightPower (535 : Fin 988) ≤ ((606206421545143 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_535
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_535 : heightFactor (535 : Fin 988) ≤ ((718773155847 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_535
  obtain ⟨hpl, hph⟩ := kernel_bounds_2376
  obtain ⟨hcl, hch⟩ := kernel_bounds_2377
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2377
  have h : (((5650129 / 2048 : ℚ) : ℝ) * (logKernel ((297 / 8 : ℚ) : ℝ) - logKernel ((2377 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2377 / 64 : ℚ) : ℝ) + Real.log ((2377 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((718773155847 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_536 : ((260497713609326635 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1189 / 32 : ℚ) : ℝ) ∧
    Real.log ((1189 / 32 : ℚ) : ℝ) ≤ ((130248856804663319 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((260497713609326635 / 72057594037927936 : ℚ) : ℝ) ≤ ((1189 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1189 / 32 : ℚ) : ℝ) ≤ Real.exp ((130248856804663319 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_536 : heightPower (536 : Fin 988) ≤ ((1214671061925409 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_536
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_536 : heightFactor (536 : Fin 988) ≤ ((350492176967 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_536
  obtain ⟨hpl, hph⟩ := kernel_bounds_2377
  obtain ⟨hcl, hch⟩ := kernel_bounds_2378
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2378
  have h : (((1413721 / 512 : ℚ) : ℝ) * (logKernel ((2377 / 64 : ℚ) : ℝ) - logKernel ((1189 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1189 / 32 : ℚ) : ℝ) + Real.log ((1189 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((350492176967 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_537 : ((130264004501762195 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2379 / 64 : ℚ) : ℝ) ∧
    Real.log ((2379 / 64 : ℚ) : ℝ) ≤ ((260528009003524393 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((130264004501762195 / 36028797018963968 : ℚ) : ℝ) ≤ ((2379 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2379 / 64 : ℚ) : ℝ) ≤ Real.exp ((260528009003524393 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_537 : heightPower (537 : Fin 988) ≤ ((2433858511745507 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_537
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_537 : heightFactor (537 : Fin 988) ≤ ((42727220137 / 17592186044416 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_537
  obtain ⟨hpl, hph⟩ := kernel_bounds_2378
  obtain ⟨hcl, hch⟩ := kernel_bounds_2379
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2379
  have h : (((5659641 / 2048 : ℚ) : ℝ) * (logKernel ((1189 / 32 : ℚ) : ℝ) - logKernel ((2379 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2379 / 64 : ℚ) : ℝ) + Real.log ((2379 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((42727220137 / 17592186044416 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_538 : ((130279145832944895 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((595 / 16 : ℚ) : ℝ) ∧
    Real.log ((595 / 16 : ℚ) : ℝ) ≤ ((260558291665889793 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((130279145832944895 / 36028797018963968 : ℚ) : ℝ) ≤ ((595 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((595 / 16 : ℚ) : ℝ) ≤ Real.exp ((260558291665889793 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_538 : heightPower (538 : Fin 988) ≤ ((2438374849906475 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_538
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_538 : heightFactor (538 : Fin 988) ≤ ((666715786063 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_538
  obtain ⟨hpl, hph⟩ := kernel_bounds_2379
  obtain ⟨hcl, hch⟩ := kernel_bounds_2380
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2380
  have h : (((354025 / 128 : ℚ) : ℝ) * (logKernel ((2379 / 64 : ℚ) : ℝ) - logKernel ((595 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((595 / 16 : ℚ) : ℝ) + Real.log ((595 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((666715786063 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_539 : ((130294280803559803 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2381 / 64 : ℚ) : ℝ) ∧
    Real.log ((2381 / 64 : ℚ) : ℝ) ≤ ((260588561607119609 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((130294280803559803 / 36028797018963968 : ℚ) : ℝ) ≤ ((2381 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2381 / 64 : ℚ) : ℝ) ≤ Real.exp ((260588561607119609 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_539 : heightPower (539 : Fin 988) ≤ ((610722784593877 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_539
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_539 : heightFactor (539 : Fin 988) ≤ ((325107269793 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_539
  obtain ⟨hpl, hph⟩ := kernel_bounds_2380
  obtain ⟨hcl, hch⟩ := kernel_bounds_2381
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2381
  have h : (((5669161 / 2048 : ℚ) : ℝ) * (logKernel ((595 / 16 : ℚ) : ℝ) - logKernel ((2381 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2381 / 64 : ℚ) : ℝ) + Real.log ((2381 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((325107269793 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_540 : ((16288676177368571 / 4503599627370496 : ℚ) : ℝ) ≤ Real.log ((1191 / 32 : ℚ) : ℝ) ∧
    Real.log ((1191 / 32 : ℚ) : ℝ) ≤ ((260618818837897139 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((16288676177368571 / 4503599627370496 : ℚ) : ℝ) ≤ ((1191 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1191 / 32 : ℚ) : ℝ) ≤ Real.exp ((260618818837897139 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_540 : heightPower (540 : Fin 988) ≤ ((2447407377194337 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_540
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_540 : heightFactor (540 : Fin 988) ≤ ((317060719383 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_540
  obtain ⟨hpl, hph⟩ := kernel_bounds_2381
  obtain ⟨hcl, hch⟩ := kernel_bounds_2382
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2382
  have h : (((1418481 / 512 : ℚ) : ℝ) * (logKernel ((2381 / 64 : ℚ) : ℝ) - logKernel ((1191 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1191 / 32 : ℚ) : ℝ) + Real.log ((1191 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((317060719383 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_541 : ((4072641615138941 / 1125899906842624 : ℚ) : ℝ) ≤ Real.log ((2383 / 64 : ℚ) : ℝ) ∧
    Real.log ((2383 / 64 : ℚ) : ℝ) ≤ ((260649063368892227 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((4072641615138941 / 1125899906842624 : ℚ) : ℝ) ≤ ((2383 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2383 / 64 : ℚ) : ℝ) ≤ Real.exp ((260649063368892227 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_541 : heightPower (541 : Fin 988) ≤ ((2451923566404641 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_541
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_541 : heightFactor (541 : Fin 988) ≤ ((618426395113 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_541
  obtain ⟨hpl, hph⟩ := kernel_bounds_2382
  obtain ⟨hcl, hch⟩ := kernel_bounds_2383
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2383
  have h : (((5678689 / 2048 : ℚ) : ℝ) * (logKernel ((1191 / 32 : ℚ) : ℝ) - logKernel ((2383 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2383 / 64 : ℚ) : ℝ) + Real.log ((2383 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((618426395113 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_542 : ((260679295210761287 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((149 / 4 : ℚ) : ℝ) ∧
    Real.log ((149 / 4 : ℚ) : ℝ) ≤ ((130339647605380645 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((260679295210761287 / 72057594037927936 : ℚ) : ℝ) ≤ ((149 / 4 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((149 / 4 : ℚ) : ℝ) ≤ Real.exp ((130339647605380645 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_542 : heightPower (542 : Fin 988) ≤ ((1228219853024023 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_542
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_542 : heightFactor (542 : Fin 988) ≤ ((301559784665 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_542
  obtain ⟨hpl, hph⟩ := kernel_bounds_2383
  obtain ⟨hcl, hch⟩ := kernel_bounds_2384
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2384
  have h : (((22201 / 8 : ℚ) : ℝ) * (logKernel ((2383 / 64 : ℚ) : ℝ) - logKernel ((149 / 4 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((149 / 4 : ℚ) : ℝ) + Real.log ((149 / 4 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((301559784665 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_543 : ((260709514374147333 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2385 / 64 : ℚ) : ℝ) ∧
    Real.log ((2385 / 64 : ℚ) : ℝ) ≤ ((32588689296768417 / 9007199254740992 : ℚ) : ℝ) := by
  have hl : Real.exp ((260709514374147333 / 72057594037927936 : ℚ) : ℝ) ≤ ((2385 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2385 / 64 : ℚ) : ℝ) ≤ Real.exp ((32588689296768417 / 9007199254740992 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_543 : heightPower (543 : Fin 988) ≤ ((2460955796166127 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_543
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_543 : heightFactor (543 : Fin 988) ≤ ((147047841291 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_543
  obtain ⟨hpl, hph⟩ := kernel_bounds_2384
  obtain ⟨hcl, hch⟩ := kernel_bounds_2385
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2385
  have h : (((5688225 / 2048 : ℚ) : ℝ) * (logKernel ((149 / 4 : ℚ) : ℝ) - logKernel ((2385 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2385 / 64 : ℚ) : ℝ) + Real.log ((2385 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((147047841291 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

end LegendreK6.M2Pilot.Enclosures.Height016
