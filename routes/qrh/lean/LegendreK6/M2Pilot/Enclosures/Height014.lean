import LegendreK6.M2PilotDefinitions
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp

/-! Generated proposals: every bound is checked by Lean, not by trusting Arb. -/
namespace LegendreK6.M2Pilot.Enclosures.Height014
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem height_z_bounds_2289 : ((8154680240227939 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2289 / 64 : ℚ) : ℝ) ∧
    heightZ ((2289 / 64 : ℚ) : ℝ) ≤ ((4077340120113971 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((8154680240227939 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2289 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1139 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2289 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1139 / 192 : ℚ) : ℝ) ≤ ((4077340120113971 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2289 : ((58143672641 / 2251799813685248 : ℚ) : ℝ) ≤ logKernel ((2289 / 64 : ℚ) : ℝ) ∧
    logKernel ((2289 / 64 : ℚ) : ℝ) ≤ ((1860597524517 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2289
  constructor
  · exact (show ((58143672641 / 2251799813685248 : ℚ) : ℝ) ≤ zKernel ((8154680240227939 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2289 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((4077340120113971 / 9223372036854775808 : ℚ) : ℝ) ≤ ((1860597524517 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2290 : ((4014126820711407 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((1145 / 32 : ℚ) : ℝ) ∧
    heightZ ((1145 / 32 : ℚ) : ℝ) ≤ ((8028253641422817 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((4014126820711407 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((1145 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-571 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1145 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-571 / 96 : ℚ) : ℝ) ≤ ((8028253641422817 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2290 : ((1803352956741 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1145 / 32 : ℚ) : ℝ) ∧
    logKernel ((1145 / 32 : ℚ) : ℝ) ≤ ((901676478373 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2290
  constructor
  · exact (show ((1803352956741 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((4014126820711407 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1145 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((8028253641422817 / 18446744073709551616 : ℚ) : ℝ) ≤ ((901676478373 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2291 : ((987973388169557 / 2305843009213693952 : ℚ) : ℝ) ≤ heightZ ((2291 / 64 : ℚ) : ℝ) ∧
    heightZ ((2291 / 64 : ℚ) : ℝ) ≤ ((7903787105356459 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((987973388169557 / 2305843009213693952 : ℚ) : ℝ) ≤ Real.exp (-((2291 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1145 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2291 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1145 / 192 : ℚ) : ℝ) ≤ ((7903787105356459 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2291 : ((1747869619165 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2291 / 64 : ℚ) : ℝ) ∧
    logKernel ((2291 / 64 : ℚ) : ℝ) ≤ ((873934809585 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2291
  constructor
  · exact (show ((1747869619165 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((987973388169557 / 2305843009213693952 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2291 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((7903787105356459 / 18446744073709551616 : ℚ) : ℝ) ≤ ((873934809585 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2292 : ((7781250244072721 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((573 / 16 : ℚ) : ℝ) ∧
    heightZ ((573 / 16 : ℚ) : ℝ) ≤ ((1945312561018181 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((7781250244072721 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((573 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-287 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((573 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-287 / 48 : ℚ) : ℝ) ≤ ((1945312561018181 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2292 : ((847046662213 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((573 / 16 : ℚ) : ℝ) ∧
    logKernel ((573 / 16 : ℚ) : ℝ) ≤ ((1694093324431 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2292
  constructor
  · exact (show ((847046662213 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((7781250244072721 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((573 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1945312561018181 / 4611686018427387904 : ℚ) : ℝ) ≤ ((1694093324431 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2293 : ((3830306570368529 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2293 / 64 : ℚ) : ℝ) ∧
    heightZ ((2293 / 64 : ℚ) : ℝ) ≤ ((7660613140737061 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((3830306570368529 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2293 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1151 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2293 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1151 / 192 : ℚ) : ℝ) ≤ ((7660613140737061 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2293 : ((820985776169 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2293 / 64 : ℚ) : ℝ) ∧
    logKernel ((2293 / 64 : ℚ) : ℝ) ≤ ((1641971552343 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2293
  constructor
  · exact (show ((820985776169 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((3830306570368529 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2293 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((7660613140737061 / 18446744073709551616 : ℚ) : ℝ) ≤ ((1641971552343 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2294 : ((7541846342332445 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1147 / 32 : ℚ) : ℝ) ∧
    heightZ ((1147 / 32 : ℚ) : ℝ) ≤ ((235682698197889 / 576460752303423488 : ℚ) : ℝ) := by
  have h : ((7541846342332445 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1147 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-577 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1147 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-577 / 96 : ℚ) : ℝ) ≤ ((235682698197889 / 576460752303423488 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2294 : ((1591453398591 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1147 / 32 : ℚ) : ℝ) ∧
    logKernel ((1147 / 32 : ℚ) : ℝ) ≤ ((397863349649 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2294
  constructor
  · exact (show ((1591453398591 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((7541846342332445 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1147 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((235682698197889 / 576460752303423488 : ℚ) : ℝ) ≤ ((397863349649 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2295 : ((1856230213117141 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((2295 / 64 : ℚ) : ℝ) ∧
    heightZ ((2295 / 64 : ℚ) : ℝ) ≤ ((7424920852468567 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((1856230213117141 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((2295 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1157 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2295 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1157 / 192 : ℚ) : ℝ) ≤ ((7424920852468567 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2295 : ((771244762517 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2295 / 64 : ℚ) : ℝ) ∧
    logKernel ((2295 / 64 : ℚ) : ℝ) ≤ ((1542489525039 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2295
  constructor
  · exact (show ((771244762517 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((1856230213117141 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2295 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((7424920852468567 / 18446744073709551616 : ℚ) : ℝ) ≤ ((1542489525039 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2296 : ((7309808124302461 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((287 / 8 : ℚ) : ℝ) ∧
    heightZ ((287 / 8 : ℚ) : ℝ) ≤ ((57107875971113 / 144115188075855872 : ℚ) : ℝ) := by
  have h : ((7309808124302461 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((287 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-145 / 24 : ℚ) : ℝ) ∧
      Real.exp (-((287 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-145 / 24 : ℚ) : ℝ) ≤ ((57107875971113 / 144115188075855872 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2296 : ((1495032111495 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((287 / 8 : ℚ) : ℝ) ∧
    logKernel ((287 / 8 : ℚ) : ℝ) ≤ ((373758027875 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2296
  constructor
  · exact (show ((1495032111495 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((7309808124302461 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((287 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((57107875971113 / 144115188075855872 : ℚ) : ℝ) ≤ ((373758027875 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2297 : ((112445000837015 / 288230376151711744 : ℚ) : ℝ) ≤ heightZ ((2297 / 64 : ℚ) : ℝ) ∧
    heightZ ((2297 / 64 : ℚ) : ℝ) ≤ ((7196480053568963 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((112445000837015 / 288230376151711744 : ℚ) : ℝ) ≤ Real.exp (-((2297 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1163 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2297 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1163 / 192 : ℚ) : ℝ) ≤ ((7196480053568963 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2297 : ((724517404535 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2297 / 64 : ℚ) : ℝ) ∧
    logKernel ((2297 / 64 : ℚ) : ℝ) ≤ ((1449034809075 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2297
  constructor
  · exact (show ((724517404535 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((112445000837015 / 288230376151711744 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2297 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((7196480053568963 / 18446744073709551616 : ℚ) : ℝ) ≤ ((1449034809075 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2298 : ((1771227242929783 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((1149 / 32 : ℚ) : ℝ) ∧
    heightZ ((1149 / 32 : ℚ) : ℝ) ≤ ((7084908971719135 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((1771227242929783 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((1149 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-583 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1149 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-583 / 96 : ℚ) : ℝ) ≤ ((7084908971719135 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2298 : ((87778293429 / 4503599627370496 : ℚ) : ℝ) ≤ logKernel ((1149 / 32 : ℚ) : ℝ) ∧
    logKernel ((1149 / 32 : ℚ) : ℝ) ≤ ((1404452694869 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2298
  constructor
  · exact (show ((87778293429 / 4503599627370496 : ℚ) : ℝ) ≤ zKernel ((1771227242929783 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1149 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((7084908971719135 / 18446744073709551616 : ℚ) : ℝ) ≤ ((1404452694869 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2299 : ((6975067639165137 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2299 / 64 : ℚ) : ℝ) ∧
    heightZ ((2299 / 64 : ℚ) : ℝ) ≤ ((1743766909791285 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((6975067639165137 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2299 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1169 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2299 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1169 / 192 : ℚ) : ℝ) ≤ ((1743766909791285 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2299 : ((85077639257 / 4503599627370496 : ℚ) : ℝ) ≤ logKernel ((2299 / 64 : ℚ) : ℝ) ∧
    logKernel ((2299 / 64 : ℚ) : ℝ) ≤ ((1361242228117 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2299
  constructor
  · exact (show ((85077639257 / 4503599627370496 : ℚ) : ℝ) ≤ zKernel ((6975067639165137 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2299 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1743766909791285 / 4611686018427387904 : ℚ) : ℝ) ≤ ((1361242228117 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2300 : ((6866929238629803 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((575 / 16 : ℚ) : ℝ) ∧
    heightZ ((575 / 16 : ℚ) : ℝ) ≤ ((3433464619314903 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((6866929238629803 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((575 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-293 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((575 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-293 / 48 : ℚ) : ℝ) ≤ ((3433464619314903 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2300 : ((659680603829 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((575 / 16 : ℚ) : ℝ) ∧
    logKernel ((575 / 16 : ℚ) : ℝ) ≤ ((1319361207663 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2300
  constructor
  · exact (show ((659680603829 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((6866929238629803 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((575 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((3433464619314903 / 9223372036854775808 : ℚ) : ℝ) ≤ ((1319361207663 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2301 : ((6760467368599303 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2301 / 64 : ℚ) : ℝ) ∧
    heightZ ((2301 / 64 : ℚ) : ℝ) ≤ ((3380233684299653 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((6760467368599303 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2301 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1175 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2301 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1175 / 192 : ℚ) : ℝ) ≤ ((3380233684299653 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2301 : ((1278768730741 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2301 / 64 : ℚ) : ℝ) ∧
    logKernel ((2301 / 64 : ℚ) : ℝ) ≤ ((639384365373 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2301
  constructor
  · exact (show ((1278768730741 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((6760467368599303 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2301 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((3380233684299653 / 9223372036854775808 : ℚ) : ℝ) ≤ ((639384365373 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2302 : ((6655656036877343 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1151 / 32 : ℚ) : ℝ) ∧
    heightZ ((1151 / 32 : ℚ) : ℝ) ≤ ((3327828018438673 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((6655656036877343 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1151 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-589 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1151 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-589 / 96 : ℚ) : ℝ) ≤ ((3327828018438673 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2302 : ((309856288261 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((1151 / 32 : ℚ) : ℝ) ∧
    logKernel ((1151 / 32 : ℚ) : ℝ) ≤ ((1239425153049 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2302
  constructor
  · exact (show ((309856288261 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((6655656036877343 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1151 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((3327828018438673 / 9223372036854775808 : ℚ) : ℝ) ≤ ((1239425153049 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2303 : ((6552469654239281 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2303 / 64 : ℚ) : ℝ) ∧
    heightZ ((2303 / 64 : ℚ) : ℝ) ≤ ((1638117413559821 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((6552469654239281 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2303 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1181 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2303 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1181 / 192 : ℚ) : ℝ) ≤ ((1638117413559821 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2303 : ((150161506247 / 9007199254740992 : ℚ) : ℝ) ≤ logKernel ((2303 / 64 : ℚ) : ℝ) ∧
    logKernel ((2303 / 64 : ℚ) : ℝ) ≤ ((1201292049981 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2303
  constructor
  · exact (show ((150161506247 / 9007199254740992 : ℚ) : ℝ) ≤ zKernel ((6552469654239281 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2303 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1638117413559821 / 4611686018427387904 : ℚ) : ℝ) ≤ ((1201292049981 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2304 : ((6450883028184633 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((36 / 1 : ℚ) : ℝ) ∧
    heightZ ((36 / 1 : ℚ) : ℝ) ≤ ((1612720757046159 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((6450883028184633 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((36 / 1 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-37 / 6 : ℚ) : ℝ) ∧
      Real.exp (-((36 / 1 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-37 / 6 : ℚ) : ℝ) ≤ ((1612720757046159 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2304 : ((1164332179149 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((36 / 1 : ℚ) : ℝ) ∧
    logKernel ((36 / 1 : ℚ) : ℝ) ≤ ((582166089577 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2304
  constructor
  · exact (show ((1164332179149 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((6450883028184633 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((36 / 1 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1612720757046159 / 4611686018427387904 : ℚ) : ℝ) ≤ ((582166089577 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2305 : ((3175435678393215 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2305 / 64 : ℚ) : ℝ) ∧
    heightZ ((2305 / 64 : ℚ) : ℝ) ≤ ((6350871356786433 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((3175435678393215 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2305 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1187 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2305 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1187 / 192 : ℚ) : ℝ) ≤ ((6350871356786433 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2305 : ((1128509444001 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2305 / 64 : ℚ) : ℝ) ∧
    logKernel ((2305 / 64 : ℚ) : ℝ) ≤ ((564254722003 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2305
  constructor
  · exact (show ((1128509444001 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((3175435678393215 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2305 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((6350871356786433 / 18446744073709551616 : ℚ) : ℝ) ≤ ((564254722003 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2306 : ((781551277829493 / 2305843009213693952 : ℚ) : ℝ) ≤ heightZ ((1153 / 32 : ℚ) : ℝ) ∧
    heightZ ((1153 / 32 : ℚ) : ℝ) ≤ ((6252410222635947 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((781551277829493 / 2305843009213693952 : ℚ) : ℝ) ≤ Real.exp (-((1153 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-595 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1153 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-595 / 96 : ℚ) : ℝ) ≤ ((6252410222635947 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2306 : ((546894429273 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((1153 / 32 : ℚ) : ℝ) ∧
    logKernel ((1153 / 32 : ℚ) : ℝ) ≤ ((1093788858551 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2306
  constructor
  · exact (show ((546894429273 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((781551277829493 / 2305843009213693952 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1153 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((6252410222635947 / 18446744073709551616 : ℚ) : ℝ) ≤ ((1093788858551 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2307 : ((24044826511255 / 72057594037927936 : ℚ) : ℝ) ≤ heightZ ((2307 / 64 : ℚ) : ℝ) ∧
    heightZ ((2307 / 64 : ℚ) : ℝ) ≤ ((6155475586881283 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((24044826511255 / 72057594037927936 : ℚ) : ℝ) ≤ Real.exp (-((2307 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1193 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2307 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1193 / 192 : ℚ) : ℝ) ≤ ((6155475586881283 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2307 : ((1060136513203 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2307 / 64 : ℚ) : ℝ) ∧
    logKernel ((2307 / 64 : ℚ) : ℝ) ≤ ((132517064151 / 9007199254740992 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2307
  constructor
  · exact (show ((1060136513203 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((24044826511255 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2307 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((6155475586881283 / 18446744073709551616 : ℚ) : ℝ) ≤ ((132517064151 / 9007199254740992 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2308 : ((6060043783358395 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((577 / 16 : ℚ) : ℝ) ∧
    heightZ ((577 / 16 : ℚ) : ℝ) ≤ ((3030021891679199 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((6060043783358395 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((577 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-299 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((577 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-299 / 48 : ℚ) : ℝ) ≤ ((3030021891679199 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2308 : ((513759770839 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((577 / 16 : ℚ) : ℝ) ∧
    logKernel ((577 / 16 : ℚ) : ℝ) ≤ ((1027519541683 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2308
  constructor
  · exact (show ((513759770839 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((6060043783358395 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((577 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((3030021891679199 / 9223372036854775808 : ℚ) : ℝ) ≤ ((1027519541683 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2309 : ((5966091512813115 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2309 / 64 : ℚ) : ℝ) ∧
    heightZ ((2309 / 64 : ℚ) : ℝ) ≤ ((2983045756406559 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((5966091512813115 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2309 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1199 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2309 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1199 / 192 : ℚ) : ℝ) ≤ ((2983045756406559 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2309 : ((248976522217 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((2309 / 64 : ℚ) : ℝ) ∧
    logKernel ((2309 / 64 : ℚ) : ℝ) ≤ ((995906088873 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2309
  constructor
  · exact (show ((248976522217 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((5966091512813115 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2309 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((2983045756406559 / 9223372036854775808 : ℚ) : ℝ) ≤ ((995906088873 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2310 : ((5873595837212719 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1155 / 32 : ℚ) : ℝ) ∧
    heightZ ((1155 / 32 : ℚ) : ℝ) ≤ ((2936797918606361 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((5873595837212719 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1155 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-601 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1155 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-601 / 96 : ℚ) : ℝ) ≤ ((2936797918606361 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2310 : ((241316319937 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((1155 / 32 : ℚ) : ℝ) ∧
    logKernel ((1155 / 32 : ℚ) : ℝ) ≤ ((965265279753 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2310
  constructor
  · exact (show ((241316319937 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((5873595837212719 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1155 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((2936797918606361 / 9223372036854775808 : ℚ) : ℝ) ≤ ((965265279753 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2311 : ((722816771768215 / 2305843009213693952 : ℚ) : ℝ) ≤ heightZ ((2311 / 64 : ℚ) : ℝ) ∧
    heightZ ((2311 / 64 : ℚ) : ℝ) ≤ ((5782534174145723 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((722816771768215 / 2305843009213693952 : ℚ) : ℝ) ≤ Real.exp (-((2311 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1205 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2311 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1205 / 192 : ℚ) : ℝ) ≤ ((5782534174145723 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2311 : ((467783594609 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2311 / 64 : ℚ) : ℝ) ∧
    logKernel ((2311 / 64 : ℚ) : ℝ) ≤ ((935567189223 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2311
  constructor
  · exact (show ((467783594609 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((722816771768215 / 2305843009213693952 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2311 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((5782534174145723 / 18446744073709551616 : ℚ) : ℝ) ≤ ((935567189223 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2312 : ((5692884291308473 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((289 / 8 : ℚ) : ℝ) ∧
    heightZ ((289 / 8 : ℚ) : ℝ) ≤ ((1423221072827119 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((5692884291308473 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((289 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-151 / 24 : ℚ) : ℝ) ∧
      Real.exp (-((289 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-151 / 24 : ℚ) : ℝ) ≤ ((1423221072827119 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2312 : ((226695703219 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((289 / 8 : ℚ) : ℝ) ∧
    logKernel ((289 / 8 : ℚ) : ℝ) ≤ ((906782812881 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2312
  constructor
  · exact (show ((226695703219 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((5692884291308473 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((289 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1423221072827119 / 4611686018427387904 : ℚ) : ℝ) ≤ ((906782812881 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2313 : ((5604624301077251 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2313 / 64 : ℚ) : ℝ) ∧
    heightZ ((2313 / 64 : ℚ) : ℝ) ≤ ((2802312150538627 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((5604624301077251 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2313 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1211 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2313 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1211 / 192 : ℚ) : ℝ) ≤ ((2802312150538627 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2313 : ((878884038691 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2313 / 64 : ℚ) : ℝ) ∧
    logKernel ((2313 / 64 : ℚ) : ℝ) ≤ ((109860504837 / 9007199254740992 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2313
  constructor
  · exact (show ((878884038691 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((5604624301077251 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2313 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((2802312150538627 / 9223372036854775808 : ℚ) : ℝ) ≤ ((109860504837 / 9007199254740992 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2314 : ((5517732655164481 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1157 / 32 : ℚ) : ℝ) ∧
    heightZ ((1157 / 32 : ℚ) : ℝ) ≤ ((1379433163791121 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((5517732655164481 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1157 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-607 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1157 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-607 / 96 : ℚ) : ℝ) ≤ ((1379433163791121 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2314 : ((425921809775 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((1157 / 32 : ℚ) : ℝ) ∧
    logKernel ((1157 / 32 : ℚ) : ℝ) ≤ ((851843619555 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2314
  constructor
  · exact (show ((425921809775 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((5517732655164481 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1157 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1379433163791121 / 4611686018427387904 : ℚ) : ℝ) ≤ ((851843619555 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2315 : ((42438969838733 / 144115188075855872 : ℚ) : ℝ) ≤ heightZ ((2315 / 64 : ℚ) : ℝ) ∧
    heightZ ((2315 / 64 : ℚ) : ℝ) ≤ ((5432188139357827 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((42438969838733 / 144115188075855872 : ℚ) : ℝ) ≤ Real.exp (-((2315 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1217 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2315 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1217 / 192 : ℚ) : ℝ) ≤ ((5432188139357827 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2315 : ((206408786661 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((2315 / 64 : ℚ) : ℝ) ∧
    logKernel ((2315 / 64 : ℚ) : ℝ) ≤ ((825635146649 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2315
  constructor
  · exact (show ((206408786661 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((42438969838733 / 144115188075855872 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2315 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((5432188139357827 / 18446744073709551616 : ℚ) : ℝ) ≤ ((825635146649 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2316 : ((334248116771301 / 1152921504606846976 : ℚ) : ℝ) ≤ heightZ ((579 / 16 : ℚ) : ℝ) ∧
    heightZ ((579 / 16 : ℚ) : ℝ) ≤ ((5347969868340819 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((334248116771301 / 1152921504606846976 : ℚ) : ℝ) ≤ Real.exp (-((579 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-305 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((579 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-305 / 48 : ℚ) : ℝ) ≤ ((5347969868340819 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2316 : ((800233023679 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((579 / 16 : ℚ) : ℝ) ∧
    logKernel ((579 / 16 : ℚ) : ℝ) ≤ ((200058255921 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2316
  constructor
  · exact (show ((800233023679 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((334248116771301 / 1152921504606846976 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((579 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((5347969868340819 / 18446744073709551616 : ℚ) : ℝ) ≤ ((200058255921 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2317 : ((5265057280593817 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2317 / 64 : ℚ) : ℝ) ∧
    heightZ ((2317 / 64 : ℚ) : ℝ) ≤ ((1316264320148455 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((5265057280593817 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2317 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1223 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2317 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1223 / 192 : ℚ) : ℝ) ≤ ((1316264320148455 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2317 : ((775612441875 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2317 / 64 : ℚ) : ℝ) ∧
    logKernel ((2317 / 64 : ℚ) : ℝ) ≤ ((96951555235 / 9007199254740992 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2317
  constructor
  · exact (show ((775612441875 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((5265057280593817 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2317 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1316264320148455 / 4611686018427387904 : ℚ) : ℝ) ≤ ((96951555235 / 9007199254740992 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2318 : ((5183430133373997 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1159 / 32 : ℚ) : ℝ) ∧
    heightZ ((1159 / 32 : ℚ) : ℝ) ≤ ((323964383335875 / 1152921504606846976 : ℚ) : ℝ) := by
  have h : ((5183430133373997 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1159 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-613 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1159 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-613 / 96 : ℚ) : ℝ) ≤ ((323964383335875 / 1152921504606846976 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2318 : ((751749355739 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1159 / 32 : ℚ) : ℝ) ∧
    logKernel ((1159 / 32 : ℚ) : ℝ) ≤ ((23492167367 / 2251799813685248 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2318
  constructor
  · exact (show ((751749355739 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((5183430133373997 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1159 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((323964383335875 / 1152921504606846976 : ℚ) : ℝ) ≤ ((23492167367 / 2251799813685248 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2319 : ((5103068497773169 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2319 / 64 : ℚ) : ℝ) ∧
    heightZ ((2319 / 64 : ℚ) : ℝ) ≤ ((1275767124443293 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((5103068497773169 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2319 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1229 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2319 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1229 / 192 : ℚ) : ℝ) ≤ ((1275767124443293 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2319 : ((364310229789 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2319 / 64 : ℚ) : ℝ) ∧
    logKernel ((2319 / 64 : ℚ) : ℝ) ≤ ((728620459583 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2319
  constructor
  · exact (show ((364310229789 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((5103068497773169 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2319 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1275767124443293 / 4611686018427387904 : ℚ) : ℝ) ≤ ((728620459583 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2320 : ((5023952753852227 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((145 / 4 : ℚ) : ℝ) ∧
    heightZ ((145 / 4 : ℚ) : ℝ) ≤ ((2511976376926115 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((5023952753852227 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((145 / 4 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-77 / 12 : ℚ) : ℝ) ∧
      Real.exp (-((145 / 4 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-77 / 12 : ℚ) : ℝ) ≤ ((2511976376926115 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2320 : ((706203164743 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((145 / 4 : ℚ) : ℝ) ∧
    logKernel ((145 / 4 : ℚ) : ℝ) ≤ ((176550791187 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2320
  constructor
  · exact (show ((706203164743 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((5023952753852227 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((145 / 4 : ℚ) : ℝ)) hh).trans
      (show zKernel ((2511976376926115 / 9223372036854775808 : ℚ) : ℝ) ≤ ((176550791187 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

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

theorem log_height_bounds_448 : ((257780567243880063 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1145 / 32 : ℚ) : ℝ) ∧
    Real.log ((1145 / 32 : ℚ) : ℝ) ≤ ((128890283621940033 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((257780567243880063 / 72057594037927936 : ℚ) : ℝ) ≤ ((1145 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1145 / 32 : ℚ) : ℝ) ≤ Real.exp ((128890283621940033 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_448 : heightPower (448 : Fin 988) ≤ ((253962522235455 / 35184372088832 : ℚ) : ℝ) := by
  have hh := log_height_bounds_448
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_448 : heightFactor (448 : Fin 988) ≤ ((1587431374575 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_448
  obtain ⟨hpl, hph⟩ := kernel_bounds_2289
  obtain ⟨hcl, hch⟩ := kernel_bounds_2290
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2290
  have h : (((1311025 / 512 : ℚ) : ℝ) * (logKernel ((2289 / 64 : ℚ) : ℝ) - logKernel ((1145 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1145 / 32 : ℚ) : ℝ) + Real.log ((1145 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1587431374575 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_449 : ((64453006643450095 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((2291 / 64 : ℚ) : ℝ) ∧
    Real.log ((2291 / 64 : ℚ) : ℝ) ≤ ((257812026573800383 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((64453006643450095 / 18014398509481984 : ℚ) : ℝ) ≤ ((2291 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2291 / 64 : ℚ) : ℝ) ≤ Real.exp ((257812026573800383 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_449 : heightPower (449 : Fin 988) ≤ ((2036221112402245 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_449
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_449 : heightFactor (449 : Fin 988) ≤ ((1548201997935 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_449
  obtain ⟨hpl, hph⟩ := kernel_bounds_2290
  obtain ⟨hcl, hch⟩ := kernel_bounds_2291
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2291
  have h : (((5248681 / 2048 : ℚ) : ℝ) * (logKernel ((1145 / 32 : ℚ) : ℝ) - logKernel ((2291 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2291 / 64 : ℚ) : ℝ) + Real.log ((2291 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1548201997935 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_450 : ((4028804252734597 / 1125899906842624 : ℚ) : ℝ) ≤ Real.log ((573 / 16 : ℚ) : ℝ) ∧
    Real.log ((573 / 16 : ℚ) : ℝ) ≤ ((257843472175014211 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((4028804252734597 / 1125899906842624 : ℚ) : ℝ) ≤ ((573 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((573 / 16 : ℚ) : ℝ) ≤ Real.exp ((257843472175014211 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_450 : heightPower (450 : Fin 988) ≤ ((2040741993293091 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_450
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_450 : heightFactor (450 : Fin 988) ≤ ((1509941405497 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_450
  obtain ⟨hpl, hph⟩ := kernel_bounds_2291
  obtain ⟨hcl, hch⟩ := kernel_bounds_2292
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2292
  have h : (((328329 / 128 : ℚ) : ℝ) * (logKernel ((2291 / 64 : ℚ) : ℝ) - logKernel ((573 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((573 / 16 : ℚ) : ℝ) + Real.log ((573 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1509941405497 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_451 : ((128937452029749305 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2293 / 64 : ℚ) : ℝ) ∧
    Real.log ((2293 / 64 : ℚ) : ℝ) ≤ ((257874904059498613 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((128937452029749305 / 36028797018963968 : ℚ) : ℝ) ≤ ((2293 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2293 / 64 : ℚ) : ℝ) ≤ Real.exp ((257874904059498613 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_451 : heightPower (451 : Fin 988) ≤ ((1022631410301481 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_451
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_451 : heightFactor (451 : Fin 988) ≤ ((5890502759773 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_451
  obtain ⟨hpl, hph⟩ := kernel_bounds_2292
  obtain ⟨hcl, hch⟩ := kernel_bounds_2293
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2293
  have h : (((5257849 / 2048 : ℚ) : ℝ) * (logKernel ((573 / 16 : ℚ) : ℝ) - logKernel ((2293 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2293 / 64 : ℚ) : ℝ) + Real.log ((2293 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((5890502759773 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_452 : ((257906322239214979 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1147 / 32 : ℚ) : ℝ) ∧
    Real.log ((1147 / 32 : ℚ) : ℝ) ≤ ((128953161119607491 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((257906322239214979 / 72057594037927936 : ℚ) : ℝ) ≤ ((1147 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1147 / 32 : ℚ) : ℝ) ≤ Real.exp ((128953161119607491 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_452 : heightPower (452 : Fin 988) ≤ ((2049783594378583 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_452
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_452 : heightFactor (452 : Fin 988) ≤ ((5744926133971 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_452
  obtain ⟨hpl, hph⟩ := kernel_bounds_2293
  obtain ⟨hcl, hch⟩ := kernel_bounds_2294
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2294
  have h : (((1315609 / 512 : ℚ) : ℝ) * (logKernel ((2293 / 64 : ℚ) : ℝ) - logKernel ((1147 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1147 / 32 : ℚ) : ℝ) + Real.log ((1147 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((5744926133971 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_453 : ((257937726726109073 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2295 / 64 : ℚ) : ℝ) ∧
    Real.log ((2295 / 64 : ℚ) : ℝ) ≤ ((64484431681527269 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((257937726726109073 / 72057594037927936 : ℚ) : ℝ) ≤ ((2295 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2295 / 64 : ℚ) : ℝ) ≤ Real.exp ((64484431681527269 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_453 : heightPower (453 : Fin 988) ≤ ((2054304314666617 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_453
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_453 : heightFactor (453 : Fin 988) ≤ ((1400736193375 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_453
  obtain ⟨hpl, hph⟩ := kernel_bounds_2294
  obtain ⟨hcl, hch⟩ := kernel_bounds_2295
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2295
  have h : (((5267025 / 2048 : ℚ) : ℝ) * (logKernel ((1147 / 32 : ℚ) : ℝ) - logKernel ((2295 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2295 / 64 : ℚ) : ℝ) + Real.log ((2295 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1400736193375 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_454 : ((64492279383027759 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((287 / 8 : ℚ) : ℝ) ∧
    Real.log ((287 / 8 : ℚ) : ℝ) ≤ ((257969117532111039 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((64492279383027759 / 18014398509481984 : ℚ) : ℝ) ≤ ((287 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((287 / 8 : ℚ) : ℝ) ≤ Real.exp ((257969117532111039 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_454 : heightPower (454 : Fin 988) ≤ ((1029412490756833 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_454
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_454 : heightFactor (454 : Fin 988) ≤ ((5464469950649 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_454
  obtain ⟨hpl, hph⟩ := kernel_bounds_2295
  obtain ⟨hcl, hch⟩ := kernel_bounds_2296
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2296
  have h : (((82369 / 32 : ℚ) : ℝ) * (logKernel ((2295 / 64 : ℚ) : ℝ) - logKernel ((287 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((287 / 8 : ℚ) : ℝ) + Real.log ((287 / 8 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((5464469950649 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_455 : ((258000494669135427 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2297 / 64 : ℚ) : ℝ) ∧
    Real.log ((2297 / 64 : ℚ) : ℝ) ≤ ((129000247334567715 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((258000494669135427 / 72057594037927936 : ℚ) : ℝ) ≤ ((2297 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2297 / 64 : ℚ) : ℝ) ≤ Real.exp ((129000247334567715 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_455 : heightPower (455 : Fin 988) ≤ ((8059943730337 / 1099511627776 : ℚ) : ℝ) := by
  have hh := log_height_bounds_455
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_455 : heightFactor (455 : Fin 988) ≤ ((1332353781449 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_455
  obtain ⟨hpl, hph⟩ := kernel_bounds_2296
  obtain ⟨hcl, hch⟩ := kernel_bounds_2297
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2297
  have h : (((5276209 / 2048 : ℚ) : ℝ) * (logKernel ((287 / 8 : ℚ) : ℝ) - logKernel ((2297 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2297 / 64 : ℚ) : ℝ) + Real.log ((2297 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1332353781449 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_456 : ((258031858149081247 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1149 / 32 : ℚ) : ℝ) ∧
    Real.log ((1149 / 32 : ℚ) : ℝ) ≤ ((129015929074540625 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((258031858149081247 / 72057594037927936 : ℚ) : ℝ) ≤ ((1149 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1149 / 32 : ℚ) : ℝ) ≤ Real.exp ((129015929074540625 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_456 : heightPower (456 : Fin 988) ≤ ((1033933077535457 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_456
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_456 : heightFactor (456 : Fin 988) ≤ ((324855993343 / 17592186044416 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_456
  obtain ⟨hpl, hph⟩ := kernel_bounds_2297
  obtain ⟨hcl, hch⟩ := kernel_bounds_2298
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2298
  have h : (((1320201 / 512 : ℚ) : ℝ) * (logKernel ((2297 / 64 : ℚ) : ℝ) - logKernel ((1149 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1149 / 32 : ℚ) : ℝ) + Real.log ((1149 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((324855993343 / 17592186044416 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_457 : ((258063207983831969 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2299 / 64 : ℚ) : ℝ) ∧
    Real.log ((2299 / 64 : ℚ) : ℝ) ≤ ((64515801995957993 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((258063207983831969 / 72057594037927936 : ℚ) : ℝ) ≤ ((2299 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2299 / 64 : ℚ) : ℝ) ≤ Real.exp ((64515801995957993 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_457 : heightPower (457 : Fin 988) ≤ ((2072386661874013 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_457
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_457 : heightFactor (457 : Fin 988) ≤ ((39603358827 / 2199023255552 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_457
  obtain ⟨hpl, hph⟩ := kernel_bounds_2298
  obtain ⟨hcl, hch⟩ := kernel_bounds_2299
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2299
  have h : (((5285401 / 2048 : ℚ) : ℝ) * (logKernel ((1149 / 32 : ℚ) : ℝ) - logKernel ((2299 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2299 / 64 : ℚ) : ℝ) + Real.log ((2299 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((39603358827 / 2199023255552 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_458 : ((129047272092627779 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((575 / 16 : ℚ) : ℝ) ∧
    Real.log ((575 / 16 : ℚ) : ℝ) ≤ ((258094544185255561 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((129047272092627779 / 36028797018963968 : ℚ) : ℝ) ≤ ((575 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((575 / 16 : ℚ) : ℝ) ≤ Real.exp ((258094544185255561 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_458 : heightPower (458 : Fin 988) ≤ ((259613389427741 / 35184372088832 : ℚ) : ℝ) := by
  have hh := log_height_bounds_458
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_458 : heightFactor (458 : Fin 988) ≤ ((19312253677 / 1099511627776 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_458
  obtain ⟨hpl, hph⟩ := kernel_bounds_2299
  obtain ⟨hcl, hch⟩ := kernel_bounds_2300
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2300
  have h : (((330625 / 128 : ℚ) : ℝ) * (logKernel ((2299 / 64 : ℚ) : ℝ) - logKernel ((575 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((575 / 16 : ℚ) : ℝ) + Real.log ((575 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((19312253677 / 1099511627776 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_459 : ((258125866765204507 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2301 / 64 : ℚ) : ℝ) ∧
    Real.log ((2301 / 64 : ℚ) : ℝ) ≤ ((129062933382602255 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((258125866765204507 / 72057594037927936 : ℚ) : ℝ) ≤ ((2301 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2301 / 64 : ℚ) : ℝ) ≤ Real.exp ((129062933382602255 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_459 : heightPower (459 : Fin 988) ≤ ((1040713757880479 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_459
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_459 : heightFactor (459 : Fin 988) ≤ ((2410869307261 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_459
  obtain ⟨hpl, hph⟩ := kernel_bounds_2300
  obtain ⟨hcl, hch⟩ := kernel_bounds_2301
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2301
  have h : (((5294601 / 2048 : ℚ) : ℝ) * (logKernel ((575 / 16 : ℚ) : ℝ) - logKernel ((2301 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2301 / 64 : ℚ) : ℝ) + Real.log ((2301 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((2410869307261 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_460 : ((258157175735515857 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1151 / 32 : ℚ) : ℝ) ∧
    Real.log ((1151 / 32 : ℚ) : ℝ) ≤ ((64539293933878965 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((258157175735515857 / 72057594037927936 : ℚ) : ℝ) ≤ ((1151 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1151 / 32 : ℚ) : ℝ) ≤ Real.exp ((64539293933878965 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_460 : heightPower (460 : Fin 988) ≤ ((521486965734335 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_460
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_460 : heightFactor (460 : Fin 988) ≤ ((4702558567603 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_460
  obtain ⟨hpl, hph⟩ := kernel_bounds_2301
  obtain ⟨hcl, hch⟩ := kernel_bounds_2302
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2302
  have h : (((1324801 / 512 : ℚ) : ℝ) * (logKernel ((2301 / 64 : ℚ) : ℝ) - logKernel ((1151 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1151 / 32 : ℚ) : ℝ) + Real.log ((1151 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((4702558567603 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_461 : ((129094235554005613 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2303 / 64 : ℚ) : ℝ) ∧
    Real.log ((2303 / 64 : ℚ) : ℝ) ≤ ((258188471108011229 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((129094235554005613 / 36028797018963968 : ℚ) : ℝ) ≤ ((2303 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2303 / 64 : ℚ) : ℝ) ≤ Real.exp ((258188471108011229 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_461 : heightPower (461 : Fin 988) ≤ ((1045234078498627 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_461
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_461 : heightFactor (461 : Fin 988) ≤ ((4586322302523 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_461
  obtain ⟨hpl, hph⟩ := kernel_bounds_2302
  obtain ⟨hcl, hch⟩ := kernel_bounds_2303
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2303
  have h : (((5303809 / 2048 : ℚ) : ℝ) * (logKernel ((1151 / 32 : ℚ) : ℝ) - logKernel ((2303 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2303 / 64 : ℚ) : ℝ) + Real.log ((2303 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((4586322302523 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_462 : ((258219752894496837 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((36 / 1 : ℚ) : ℝ) ∧
    Real.log ((36 / 1 : ℚ) : ℝ) ≤ ((32277469111812105 / 9007199254740992 : ℚ) : ℝ) := by
  have hl : Real.exp ((258219752894496837 / 72057594037927936 : ℚ) : ℝ) ≤ ((36 / 1 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((36 / 1 : ℚ) : ℝ) ≤ Real.exp ((32277469111812105 / 9007199254740992 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_462 : heightPower (462 : Fin 988) ≤ ((1047494198993409 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_462
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_462 : heightFactor (462 : Fin 988) ≤ ((1118239289669 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_462
  obtain ⟨hpl, hph⟩ := kernel_bounds_2303
  obtain ⟨hcl, hch⟩ := kernel_bounds_2304
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2304
  have h : (((2592 / 1 : ℚ) : ℝ) * (logKernel ((2303 / 64 : ℚ) : ℝ) - logKernel ((36 / 1 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((36 / 1 : ℚ) : ℝ) + Real.log ((36 / 1 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1118239289669 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_463 : ((129125510553381771 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2305 / 64 : ℚ) : ℝ) ∧
    Real.log ((2305 / 64 : ℚ) : ℝ) ≤ ((258251021106763545 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((129125510553381771 / 36028797018963968 : ℚ) : ℝ) ≤ ((2305 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2305 / 64 : ℚ) : ℝ) ≤ Real.exp ((258251021106763545 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_463 : heightPower (463 : Fin 988) ≤ ((2099508585952089 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_463
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_463 : heightFactor (463 : Fin 988) ≤ ((2181196133799 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_463
  obtain ⟨hpl, hph⟩ := kernel_bounds_2304
  obtain ⟨hcl, hch⟩ := kernel_bounds_2305
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2305
  have h : (((5313025 / 2048 : ℚ) : ℝ) * (logKernel ((36 / 1 : ℚ) : ℝ) - logKernel ((2305 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2305 / 64 : ℚ) : ℝ) + Real.log ((2305 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((2181196133799 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_464 : ((64570568939146713 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((1153 / 32 : ℚ) : ℝ) ∧
    Real.log ((1153 / 32 : ℚ) : ℝ) ≤ ((258282275756586855 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((64570568939146713 / 18014398509481984 : ℚ) : ℝ) ≤ ((1153 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1153 / 32 : ℚ) : ℝ) ≤ Real.exp ((258282275756586855 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_464 : heightPower (464 : Fin 988) ≤ ((2104028720939065 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_464
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_464 : heightFactor (464 : Fin 988) ≤ ((4254558508795 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_464
  obtain ⟨hpl, hph⟩ := kernel_bounds_2305
  obtain ⟨hcl, hch⟩ := kernel_bounds_2306
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2306
  have h : (((1329409 / 512 : ℚ) : ℝ) * (logKernel ((2305 / 64 : ℚ) : ℝ) - logKernel ((1153 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1153 / 32 : ℚ) : ℝ) + Real.log ((1153 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((4254558508795 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_465 : ((258313516855726961 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2307 / 64 : ℚ) : ℝ) ∧
    Real.log ((2307 / 64 : ℚ) : ℝ) ≤ ((64578379213931741 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((258313516855726961 / 72057594037927936 : ℚ) : ℝ) ≤ ((2307 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2307 / 64 : ℚ) : ℝ) ≤ Real.exp ((64578379213931741 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_465 : heightPower (465 : Fin 988) ≤ ((2108548802993685 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_465
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_465 : heightFactor (465 : Fin 988) ≤ ((4149388466669 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_465
  obtain ⟨hpl, hph⟩ := kernel_bounds_2306
  obtain ⟨hcl, hch⟩ := kernel_bounds_2307
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2307
  have h : (((5322249 / 2048 : ℚ) : ℝ) * (logKernel ((1153 / 32 : ℚ) : ℝ) - logKernel ((2307 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2307 / 64 : ℚ) : ℝ) + Real.log ((2307 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((4149388466669 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_466 : ((129172372207964387 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((577 / 16 : ℚ) : ℝ) ∧
    Real.log ((577 / 16 : ℚ) : ℝ) ≤ ((258344744415928777 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((129172372207964387 / 36028797018963968 : ℚ) : ℝ) ≤ ((577 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((577 / 16 : ℚ) : ℝ) ≤ Real.exp ((258344744415928777 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_466 : heightPower (466 : Fin 988) ≤ ((2113068832161827 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_466
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_466 : heightFactor (466 : Fin 988) ≤ ((4046816388491 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_466
  obtain ⟨hpl, hph⟩ := kernel_bounds_2307
  obtain ⟨hcl, hch⟩ := kernel_bounds_2308
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2308
  have h : (((332929 / 128 : ℚ) : ℝ) * (logKernel ((2307 / 64 : ℚ) : ℝ) - logKernel ((577 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((577 / 16 : ℚ) : ℝ) + Real.log ((577 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((4046816388491 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_467 : ((258375958448921933 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2309 / 64 : ℚ) : ℝ) ∧
    Real.log ((2309 / 64 : ℚ) : ℝ) ≤ ((16148497403057621 / 4503599627370496 : ℚ) : ℝ) := by
  have hl : Real.exp ((258375958448921933 / 72057594037927936 : ℚ) : ℝ) ≤ ((2309 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2309 / 64 : ℚ) : ℝ) ≤ Real.exp ((16148497403057621 / 4503599627370496 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_467 : heightPower (467 : Fin 988) ≤ ((2117588808489311 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_467
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_467 : heightFactor (467 : Fin 988) ≤ ((986694535855 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_467
  obtain ⟨hpl, hph⟩ := kernel_bounds_2308
  obtain ⟨hcl, hch⟩ := kernel_bounds_2309
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2309
  have h : (((5331481 / 2048 : ℚ) : ℝ) * (logKernel ((577 / 16 : ℚ) : ℝ) - logKernel ((2309 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2309 / 64 : ℚ) : ℝ) + Real.log ((2309 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((986694535855 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_468 : ((258407158966420843 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1155 / 32 : ℚ) : ℝ) ∧
    Real.log ((1155 / 32 : ℚ) : ℝ) ≤ ((129203579483210423 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((258407158966420843 / 72057594037927936 : ℚ) : ℝ) ≤ ((1155 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1155 / 32 : ℚ) : ℝ) ≤ Real.exp ((129203579483210423 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_468 : heightPower (468 : Fin 988) ≤ ((2122108732021895 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_468
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_468 : heightFactor (468 : Fin 988) ≤ ((1924605591263 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_468
  obtain ⟨hpl, hph⟩ := kernel_bounds_2309
  obtain ⟨hcl, hch⟩ := kernel_bounds_2310
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2310
  have h : (((1334025 / 512 : ℚ) : ℝ) * (logKernel ((2309 / 64 : ℚ) : ℝ) - logKernel ((1155 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1155 / 32 : ℚ) : ℝ) + Real.log ((1155 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1924605591263 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_469 : ((129219172990062349 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2311 / 64 : ℚ) : ℝ) ∧
    Real.log ((2311 / 64 : ℚ) : ℝ) ≤ ((258438345980124701 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((129219172990062349 / 36028797018963968 : ℚ) : ℝ) ≤ ((2311 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2311 / 64 : ℚ) : ℝ) ≤ Real.exp ((258438345980124701 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_469 : heightPower (469 : Fin 988) ≤ ((66457143837665 / 8796093022208 : ℚ) : ℝ) := by
  have hh := log_height_bounds_469
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_469 : heightFactor (469 : Fin 988) ≤ ((469256812475 / 35184372088832 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_469
  obtain ⟨hpl, hph⟩ := kernel_bounds_2310
  obtain ⟨hcl, hch⟩ := kernel_bounds_2311
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2311
  have h : (((5340721 / 2048 : ℚ) : ℝ) * (logKernel ((1155 / 32 : ℚ) : ℝ) - logKernel ((2311 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2311 / 64 : ℚ) : ℝ) + Real.log ((2311 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((469256812475 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_470 : ((258469519501717509 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((289 / 8 : ℚ) : ℝ) ∧
    Real.log ((289 / 8 : ℚ) : ℝ) ≤ ((32308689937714689 / 9007199254740992 : ℚ) : ℝ) := by
  have hl : Real.exp ((258469519501717509 / 72057594037927936 : ℚ) : ℝ) ≤ ((289 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((289 / 8 : ℚ) : ℝ) ≤ Real.exp ((32308689937714689 / 9007199254740992 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_470 : heightPower (470 : Fin 988) ≤ ((1065574210442553 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_470
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_470 : heightFactor (470 : Fin 988) ≤ ((3661248594121 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_470
  obtain ⟨hpl, hph⟩ := kernel_bounds_2311
  obtain ⟨hcl, hch⟩ := kernel_bounds_2312
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2312
  have h : (((83521 / 32 : ℚ) : ℝ) * (logKernel ((2311 / 64 : ℚ) : ℝ) - logKernel ((289 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((289 / 8 : ℚ) : ℝ) + Real.log ((289 / 8 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((3661248594121 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_471 : ((258500679542868131 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2313 / 64 : ℚ) : ℝ) ∧
    Real.log ((2313 / 64 : ℚ) : ℝ) ≤ ((129250339771434067 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((258500679542868131 / 72057594037927936 : ℚ) : ℝ) ≤ ((2313 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2313 / 64 : ℚ) : ℝ) ≤ Real.exp ((129250339771434067 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_471 : heightPower (471 : Fin 988) ≤ ((1067834093153477 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_471
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_471 : heightFactor (471 : Fin 988) ≤ ((3570735432163 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_471
  obtain ⟨hpl, hph⟩ := kernel_bounds_2312
  obtain ⟨hcl, hch⟩ := kernel_bounds_2313
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2313
  have h : (((5349969 / 2048 : ℚ) : ℝ) * (logKernel ((289 / 8 : ℚ) : ℝ) - logKernel ((2313 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2313 / 64 : ℚ) : ℝ) + Real.log ((2313 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((3570735432163 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_472 : ((64632956528807571 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((1157 / 32 : ℚ) : ℝ) ∧
    Real.log ((1157 / 32 : ℚ) : ℝ) ≤ ((258531826115230287 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((64632956528807571 / 18014398509481984 : ℚ) : ℝ) ≤ ((1157 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1157 / 32 : ℚ) : ℝ) ≤ Real.exp ((258531826115230287 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_472 : heightPower (472 : Fin 988) ≤ ((535046974779087 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_472
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_472 : heightFactor (472 : Fin 988) ≤ ((1741229206107 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_472
  obtain ⟨hpl, hph⟩ := kernel_bounds_2313
  obtain ⟨hcl, hch⟩ := kernel_bounds_2314
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2314
  have h : (((1338649 / 512 : ℚ) : ℝ) * (logKernel ((2313 / 64 : ℚ) : ℝ) - logKernel ((1157 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1157 / 32 : ℚ) : ℝ) + Real.log ((1157 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1741229206107 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_473 : ((129281479615221293 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2315 / 64 : ℚ) : ℝ) ∧
    Real.log ((2315 / 64 : ℚ) : ℝ) ≤ ((258562959230442589 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((129281479615221293 / 36028797018963968 : ℚ) : ℝ) ≤ ((2315 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2315 / 64 : ℚ) : ℝ) ≤ Real.exp ((258562959230442589 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_473 : heightPower (473 : Fin 988) ≤ ((1072353779679375 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_473
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_473 : heightFactor (473 : Fin 988) ≤ ((3396362328889 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_473
  obtain ⟨hpl, hph⟩ := kernel_bounds_2314
  obtain ⟨hcl, hch⟩ := kernel_bounds_2315
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2315
  have h : (((5359225 / 2048 : ℚ) : ℝ) * (logKernel ((1157 / 32 : ℚ) : ℝ) - logKernel ((2315 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2315 / 64 : ℚ) : ℝ) + Real.log ((2315 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((3396362328889 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_474 : ((129297039450064287 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((579 / 16 : ℚ) : ℝ) ∧
    Real.log ((579 / 16 : ℚ) : ℝ) ≤ ((258594078900128577 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((129297039450064287 / 36028797018963968 : ℚ) : ℝ) ≤ ((579 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((579 / 16 : ℚ) : ℝ) ≤ Real.exp ((258594078900128577 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_474 : heightPower (474 : Fin 988) ≤ ((2149227167079565 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_474
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_474 : heightFactor (474 : Fin 988) ≤ ((3312393338705 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_474
  obtain ⟨hpl, hph⟩ := kernel_bounds_2315
  obtain ⟨hcl, hch⟩ := kernel_bounds_2316
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2316
  have h : (((335241 / 128 : ℚ) : ℝ) * (logKernel ((2315 / 64 : ℚ) : ℝ) - logKernel ((579 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((579 / 16 : ℚ) : ℝ) + Real.log ((579 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((3312393338705 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_475 : ((64656296283974183 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((2317 / 64 : ℚ) : ℝ) ∧
    Real.log ((2317 / 64 : ℚ) : ℝ) ≤ ((258625185135896735 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((64656296283974183 / 18014398509481984 : ℚ) : ℝ) ≤ ((2317 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2317 / 64 : ℚ) : ℝ) ≤ Real.exp ((258625185135896735 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_475 : heightPower (475 : Fin 988) ≤ ((1076873361162069 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_475
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_475 : heightFactor (475 : Fin 988) ≤ ((3230498926511 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_475
  obtain ⟨hpl, hph⟩ := kernel_bounds_2316
  obtain ⟨hcl, hch⟩ := kernel_bounds_2317
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2317
  have h : (((5368489 / 2048 : ℚ) : ℝ) * (logKernel ((579 / 16 : ℚ) : ℝ) - logKernel ((2317 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2317 / 64 : ℚ) : ℝ) + Real.log ((2317 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((3230498926511 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_476 : ((258656277949340517 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1159 / 32 : ℚ) : ℝ) ∧
    Real.log ((1159 / 32 : ℚ) : ℝ) ≤ ((32332034743667565 / 9007199254740992 : ℚ) : ℝ) := by
  have hl : Real.exp ((258656277949340517 / 72057594037927936 : ℚ) : ℝ) ≤ ((1159 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1159 / 32 : ℚ) : ℝ) ≤ Real.exp ((32332034743667565 / 9007199254740992 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_476 : heightPower (476 : Fin 988) ≤ ((2158266225137757 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_476
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_476 : heightFactor (476 : Fin 988) ≤ ((3150627872745 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_476
  obtain ⟨hpl, hph⟩ := kernel_bounds_2317
  obtain ⟨hcl, hch⟩ := kernel_bounds_2318
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2318
  have h : (((1343281 / 512 : ℚ) : ℝ) * (logKernel ((2317 / 64 : ℚ) : ℝ) - logKernel ((1159 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1159 / 32 : ℚ) : ℝ) + Real.log ((1159 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((3150627872745 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_477 : ((258687357352038385 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2319 / 64 : ℚ) : ℝ) ∧
    Real.log ((2319 / 64 : ℚ) : ℝ) ≤ ((64671839338009597 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((258687357352038385 / 72057594037927936 : ℚ) : ℝ) ≤ ((2319 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2319 / 64 : ℚ) : ℝ) ≤ Real.exp ((64671839338009597 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_477 : heightPower (477 : Fin 988) ≤ ((2162785675565649 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_477
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_477 : heightFactor (477 : Fin 988) ≤ ((3072730221491 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_477
  obtain ⟨hpl, hph⟩ := kernel_bounds_2318
  obtain ⟨hcl, hch⟩ := kernel_bounds_2319
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2319
  have h : (((5377761 / 2048 : ℚ) : ℝ) * (logKernel ((1159 / 32 : ℚ) : ℝ) - logKernel ((2319 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2319 / 64 : ℚ) : ℝ) + Real.log ((2319 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((3072730221491 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_478 : ((129359211677776909 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((145 / 4 : ℚ) : ℝ) ∧
    Real.log ((145 / 4 : ℚ) : ℝ) ≤ ((258718423355553821 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((129359211677776909 / 36028797018963968 : ℚ) : ℝ) ≤ ((145 / 4 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((145 / 4 : ℚ) : ℝ) ≤ Real.exp ((258718423355553821 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_478 : heightPower (478 : Fin 988) ≤ ((1083652536826493 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_478
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_478 : heightFactor (478 : Fin 988) ≤ ((187297328083 / 17592186044416 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_478
  obtain ⟨hpl, hph⟩ := kernel_bounds_2319
  obtain ⟨hcl, hch⟩ := kernel_bounds_2320
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2320
  have h : (((21025 / 8 : ℚ) : ℝ) * (logKernel ((2319 / 64 : ℚ) : ℝ) - logKernel ((145 / 4 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((145 / 4 : ℚ) : ℝ) + Real.log ((145 / 4 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((187297328083 / 17592186044416 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_479 : ((16171842248214709 / 4503599627370496 : ℚ) : ℝ) ≤ Real.log ((2321 / 64 : ℚ) : ℝ) ∧
    Real.log ((2321 / 64 : ℚ) : ℝ) ≤ ((258749475971435347 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((16171842248214709 / 4503599627370496 : ℚ) : ℝ) ≤ ((2321 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2321 / 64 : ℚ) : ℝ) ≤ Real.exp ((258749475971435347 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_479 : heightPower (479 : Fin 988) ≤ ((2171824419444877 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_479
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_479 : heightFactor (479 : Fin 988) ≤ ((730665358737 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_479
  obtain ⟨hpl, hph⟩ := kernel_bounds_2320
  obtain ⟨hcl, hch⟩ := kernel_bounds_2321
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2321
  have h : (((5387041 / 2048 : ℚ) : ℝ) * (logKernel ((145 / 4 : ℚ) : ℝ) - logKernel ((2321 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2321 / 64 : ℚ) : ℝ) + Real.log ((2321 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((730665358737 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

end LegendreK6.M2Pilot.Enclosures.Height014
