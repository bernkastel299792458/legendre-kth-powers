import LegendreK6.M2PilotDefinitions
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp

/-! Generated proposals: every bound is checked by Lean, not by trusting Arb. -/
namespace LegendreK6.M2Pilot.Enclosures.Height003
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem height_z_bounds_1937 : ((1995384464978231591 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1937 / 64 : ℚ) : ℝ) ∧
    heightZ ((1937 / 64 : ℚ) : ℝ) ≤ ((997692232489115797 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((1995384464978231591 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1937 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-83 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((1937 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-83 / 192 : ℚ) : ℝ) ≤ ((997692232489115797 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1937 : ((16091810201437349 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1937 / 64 : ℚ) : ℝ) ∧
    logKernel ((1937 / 64 : ℚ) : ℝ) ≤ ((8045905100718677 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1937
  constructor
  · exact (show ((16091810201437349 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((1995384464978231591 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1937 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((997692232489115797 / 9223372036854775808 : ℚ) : ℝ) ≤ ((8045905100718677 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1938 : ((1964448896227012133 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((969 / 32 : ℚ) : ℝ) ∧
    heightZ ((969 / 32 : ℚ) : ℝ) ≤ ((245556112028376517 / 2305843009213693952 : ℚ) : ℝ) := by
  have h : ((1964448896227012133 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((969 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-43 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((969 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-43 / 96 : ℚ) : ℝ) ≤ ((245556112028376517 / 2305843009213693952 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1938 : ((15842329808282353 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((969 / 32 : ℚ) : ℝ) ∧
    logKernel ((969 / 32 : ℚ) : ℝ) ≤ ((7921164904141179 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1938
  constructor
  · exact (show ((15842329808282353 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((1964448896227012133 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((969 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((245556112028376517 / 2305843009213693952 : ℚ) : ℝ) ≤ ((7921164904141179 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1939 : ((966996469507350363 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((1939 / 64 : ℚ) : ℝ) ∧
    heightZ ((1939 / 64 : ℚ) : ℝ) ≤ ((1933992939014700729 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((966996469507350363 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((1939 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-89 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((1939 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-89 / 192 : ℚ) : ℝ) ≤ ((1933992939014700729 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1939 : ((1949589656264819 / 9007199254740992 : ℚ) : ℝ) ≤ logKernel ((1939 / 64 : ℚ) : ℝ) ∧
    logKernel ((1939 / 64 : ℚ) : ℝ) ≤ ((15596717250118557 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1939
  constructor
  · exact (show ((1949589656264819 / 9007199254740992 : ℚ) : ℝ) ≤ zKernel ((966996469507350363 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1939 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1933992939014700729 / 18446744073709551616 : ℚ) : ℝ) ≤ ((15596717250118557 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1940 : ((952004578826795487 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((485 / 16 : ℚ) : ℝ) ∧
    heightZ ((485 / 16 : ℚ) : ℝ) ≤ ((1904009157653590977 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((952004578826795487 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((485 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-23 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((485 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-23 / 48 : ℚ) : ℝ) ≤ ((1904009157653590977 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1940 : ((15354912561722505 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((485 / 16 : ℚ) : ℝ) ∧
    logKernel ((485 / 16 : ℚ) : ℝ) ≤ ((7677456280861255 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1940
  constructor
  · exact (show ((15354912561722505 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((952004578826795487 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((485 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1904009157653590977 / 18446744073709551616 : ℚ) : ℝ) ≤ ((7677456280861255 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1941 : ((1874490231735629249 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1941 / 64 : ℚ) : ℝ) ∧
    heightZ ((1941 / 64 : ℚ) : ℝ) ≤ ((468622557933907313 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((1874490231735629249 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1941 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-95 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((1941 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-95 / 192 : ℚ) : ℝ) ≤ ((468622557933907313 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1941 : ((15116856707545395 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1941 / 64 : ℚ) : ℝ) ∧
    logKernel ((1941 / 64 : ℚ) : ℝ) ≤ ((1889607088443175 / 9007199254740992 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1941
  constructor
  · exact (show ((15116856707545395 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((1874490231735629249 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1941 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((468622557933907313 / 4611686018427387904 : ℚ) : ℝ) ≤ ((1889607088443175 / 9007199254740992 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1942 : ((1845428954345169325 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((971 / 32 : ℚ) : ℝ) ∧
    heightZ ((971 / 32 : ℚ) : ℝ) ≤ ((115339309646573083 / 1152921504606846976 : ℚ) : ℝ) := by
  have h : ((1845428954345169325 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((971 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-49 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((971 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-49 / 96 : ℚ) : ℝ) ≤ ((115339309646573083 / 1152921504606846976 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1942 : ((7441245783649875 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((971 / 32 : ℚ) : ℝ) ∧
    logKernel ((971 / 32 : ℚ) : ℝ) ≤ ((14882491567299755 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1942
  constructor
  · exact (show ((7441245783649875 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((1845428954345169325 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((971 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((115339309646573083 / 1152921504606846976 : ℚ) : ℝ) ≤ ((14882491567299755 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1943 : ((908409115149717849 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((1943 / 64 : ℚ) : ℝ) ∧
    heightZ ((1943 / 64 : ℚ) : ℝ) ≤ ((1816818230299435701 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((908409115149717849 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((1943 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-101 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((1943 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-101 / 192 : ℚ) : ℝ) ≤ ((1816818230299435701 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1943 : ((1831469990221205 / 9007199254740992 : ℚ) : ℝ) ≤ logKernel ((1943 / 64 : ℚ) : ℝ) ∧
    logKernel ((1943 / 64 : ℚ) : ℝ) ≤ ((14651759921769645 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1943
  constructor
  · exact (show ((1831469990221205 / 9007199254740992 : ℚ) : ℝ) ≤ zKernel ((908409115149717849 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1943 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1816818230299435701 / 18446744073709551616 : ℚ) : ℝ) ≤ ((14651759921769645 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1944 : ((894325537208132989 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((243 / 8 : ℚ) : ℝ) ∧
    heightZ ((243 / 8 : ℚ) : ℝ) ≤ ((1788651074416265981 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((894325537208132989 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((243 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-13 / 24 : ℚ) : ℝ) ∧
      Real.exp (-((243 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-13 / 24 : ℚ) : ℝ) ≤ ((1788651074416265981 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1944 : ((3606151359710213 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((243 / 8 : ℚ) : ℝ) ∧
    logKernel ((243 / 8 : ℚ) : ℝ) ≤ ((14424605438840857 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1944
  constructor
  · exact (show ((3606151359710213 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((894325537208132989 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((243 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1788651074416265981 / 18446744073709551616 : ℚ) : ℝ) ≤ ((14424605438840857 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1945 : ((880460304904354731 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((1945 / 64 : ℚ) : ℝ) ∧
    heightZ ((1945 / 64 : ℚ) : ℝ) ≤ ((1760920609808709465 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((880460304904354731 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((1945 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-107 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((1945 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-107 / 192 : ℚ) : ℝ) ≤ ((1760920609808709465 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1945 : ((7100486329873827 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((1945 / 64 : ℚ) : ℝ) ∧
    logKernel ((1945 / 64 : ℚ) : ℝ) ≤ ((14200972659747659 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1945
  constructor
  · exact (show ((7100486329873827 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((880460304904354731 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1945 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1760920609808709465 / 18446744073709551616 : ℚ) : ℝ) ≤ ((14200972659747659 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1946 : ((866810033103032745 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((973 / 32 : ℚ) : ℝ) ∧
    heightZ ((973 / 32 : ℚ) : ℝ) ≤ ((1733620066206065493 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((866810033103032745 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((973 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-55 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((973 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-55 / 96 : ℚ) : ℝ) ≤ ((1733620066206065493 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1946 : ((873800436595799 / 4503599627370496 : ℚ) : ℝ) ≤ logKernel ((973 / 32 : ℚ) : ℝ) ∧
    logKernel ((973 / 32 : ℚ) : ℝ) ≤ ((13980806985532789 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1946
  constructor
  · exact (show ((873800436595799 / 4503599627370496 : ℚ) : ℝ) ≤ zKernel ((866810033103032745 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((973 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1733620066206065493 / 18446744073709551616 : ℚ) : ℝ) ≤ ((13980806985532789 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1947 : ((213342847287618963 / 2305843009213693952 : ℚ) : ℝ) ≤ heightZ ((1947 / 64 : ℚ) : ℝ) ∧
    heightZ ((1947 / 64 : ℚ) : ℝ) ≤ ((1706742778300951707 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((213342847287618963 / 2305843009213693952 : ℚ) : ℝ) ≤ Real.exp (-((1947 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-113 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((1947 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-113 / 192 : ℚ) : ℝ) ≤ ((1706742778300951707 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1947 : ((6882027331858675 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((1947 / 64 : ℚ) : ℝ) ∧
    logKernel ((1947 / 64 : ℚ) : ℝ) ≤ ((13764054663717355 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1947
  constructor
  · exact (show ((6882027331858675 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((213342847287618963 / 2305843009213693952 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1947 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1706742778300951707 / 18446744073709551616 : ℚ) : ℝ) ≤ ((13764054663717355 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1948 : ((52508818253812457 / 576460752303423488 : ℚ) : ℝ) ≤ heightZ ((487 / 16 : ℚ) : ℝ) ∧
    heightZ ((487 / 16 : ℚ) : ℝ) ≤ ((1680282184121998627 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((52508818253812457 / 576460752303423488 : ℚ) : ℝ) ≤ Real.exp (-((487 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-29 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((487 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-29 / 48 : ℚ) : ℝ) ≤ ((1680282184121998627 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1948 : ((6775331387588703 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((487 / 16 : ℚ) : ℝ) ∧
    logKernel ((487 / 16 : ℚ) : ℝ) ≤ ((13550662775177411 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1948
  constructor
  · exact (show ((6775331387588703 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((52508818253812457 / 576460752303423488 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((487 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1680282184121998627 / 18446744073709551616 : ℚ) : ℝ) ≤ ((13550662775177411 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1949 : ((1654231823431773267 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1949 / 64 : ℚ) : ℝ) ∧
    heightZ ((1949 / 64 : ℚ) : ℝ) ≤ ((827115911715886635 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((1654231823431773267 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1949 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-119 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((1949 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-119 / 192 : ℚ) : ℝ) ≤ ((827115911715886635 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1949 : ((13340579221223975 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1949 / 64 : ℚ) : ℝ) ∧
    logKernel ((1949 / 64 : ℚ) : ℝ) ≤ ((3335144805305995 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1949
  constructor
  · exact (show ((13340579221223975 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((1654231823431773267 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1949 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((827115911715886635 / 9223372036854775808 : ℚ) : ℝ) ≤ ((3335144805305995 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1950 : ((1628585336149540651 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((975 / 32 : ℚ) : ℝ) ∧
    heightZ ((975 / 32 : ℚ) : ℝ) ≤ ((814292668074770327 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((1628585336149540651 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((975 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-61 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((975 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-61 / 96 : ℚ) : ℝ) ≤ ((814292668074770327 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1950 : ((6566876355441695 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((975 / 32 : ℚ) : ℝ) ∧
    logKernel ((975 / 32 : ℚ) : ℝ) ≤ ((13133752710883395 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1950
  constructor
  · exact (show ((6566876355441695 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((1628585336149540651 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((975 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((814292668074770327 / 9223372036854775808 : ℚ) : ℝ) ≤ ((13133752710883395 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1951 : ((1603336460798478121 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1951 / 64 : ℚ) : ℝ) ∧
    heightZ ((1951 / 64 : ℚ) : ℝ) ≤ ((400834115199619531 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((1603336460798478121 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1951 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-125 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((1951 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-125 / 192 : ℚ) : ℝ) ≤ ((400834115199619531 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1951 : ((12930132748374821 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1951 / 64 : ℚ) : ℝ) ∧
    logKernel ((1951 / 64 : ℚ) : ℝ) ≤ ((6465066374187413 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1951
  constructor
  · exact (show ((12930132748374821 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((1603336460798478121 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1951 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((400834115199619531 / 4611686018427387904 : ℚ) : ℝ) ≤ ((6465066374187413 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1952 : ((394619758244240845 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((61 / 2 : ℚ) : ℝ) ∧
    heightZ ((61 / 2 : ℚ) : ℝ) ≤ ((1578479032976963383 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((394619758244240845 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((61 / 2 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2 / 3 : ℚ) : ℝ) ∧
      Real.exp (-((61 / 2 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2 / 3 : ℚ) : ℝ) ≤ ((1578479032976963383 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1952 : ((1591208702597745 / 9007199254740992 : ℚ) : ℝ) ≤ logKernel ((61 / 2 : ℚ) : ℝ) ∧
    logKernel ((61 / 2 : ℚ) : ℝ) ≤ ((12729669620781965 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1952
  constructor
  · exact (show ((1591208702597745 / 9007199254740992 : ℚ) : ℝ) ≤ zKernel ((394619758244240845 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((61 / 2 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1578479032976963383 / 18446744073709551616 : ℚ) : ℝ) ≤ ((12729669620781965 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1953 : ((777003491926781503 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((1953 / 64 : ℚ) : ℝ) ∧
    heightZ ((1953 / 64 : ℚ) : ℝ) ≤ ((1554006983853563009 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((777003491926781503 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((1953 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-131 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((1953 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-131 / 192 : ℚ) : ℝ) ≤ ((1554006983853563009 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1953 : ((3133078596478957 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((1953 / 64 : ℚ) : ℝ) ∧
    logKernel ((1953 / 64 : ℚ) : ℝ) ≤ ((12532314385915833 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1953
  constructor
  · exact (show ((3133078596478957 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((777003491926781503 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1953 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1554006983853563009 / 18446744073709551616 : ℚ) : ℝ) ≤ ((12532314385915833 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1954 : ((764957169342677005 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((977 / 32 : ℚ) : ℝ) ∧
    heightZ ((977 / 32 : ℚ) : ℝ) ≤ ((1529914338685354013 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((764957169342677005 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((977 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-67 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((977 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-67 / 96 : ℚ) : ℝ) ≤ ((1529914338685354013 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1954 : ((3084504715091439 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((977 / 32 : ℚ) : ℝ) ∧
    logKernel ((977 / 32 : ℚ) : ℝ) ≤ ((12338018860365761 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1954
  constructor
  · exact (show ((3084504715091439 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((764957169342677005 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((977 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1529914338685354013 / 18446744073709551616 : ℚ) : ℝ) ≤ ((12338018860365761 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1955 : ((376548803839804171 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((1955 / 64 : ℚ) : ℝ) ∧
    heightZ ((1955 / 64 : ℚ) : ℝ) ≤ ((1506195215359216687 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((376548803839804171 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((1955 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-137 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((1955 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-137 / 192 : ℚ) : ℝ) ≤ ((1506195215359216687 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1955 : ((189792743870869 / 1125899906842624 : ℚ) : ℝ) ≤ logKernel ((1955 / 64 : ℚ) : ℝ) ∧
    logKernel ((1955 / 64 : ℚ) : ℝ) ≤ ((12146735607735621 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1955
  constructor
  · exact (show ((189792743870869 / 1125899906842624 : ℚ) : ℝ) ≤ zKernel ((376548803839804171 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1955 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1506195215359216687 / 18446744073709551616 : ℚ) : ℝ) ≤ ((12146735607735621 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1956 : ((185355477869467827 / 2305843009213693952 : ℚ) : ℝ) ≤ heightZ ((489 / 16 : ℚ) : ℝ) ∧
    heightZ ((489 / 16 : ℚ) : ℝ) ≤ ((1482843822955742619 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((185355477869467827 / 2305843009213693952 : ℚ) : ℝ) ≤ Real.exp (-((489 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-35 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((489 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-35 / 48 : ℚ) : ℝ) ≤ ((1482843822955742619 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1956 : ((5979208963531219 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((489 / 16 : ℚ) : ℝ) ∧
    logKernel ((489 / 16 : ℚ) : ℝ) ≤ ((11958417927062443 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1956
  constructor
  · exact (show ((5979208963531219 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((185355477869467827 / 2305843009213693952 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((489 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1482843822955742619 / 18446744073709551616 : ℚ) : ℝ) ≤ ((11958417927062443 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1957 : ((364963615083851809 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((1957 / 64 : ℚ) : ℝ) ∧
    heightZ ((1957 / 64 : ℚ) : ℝ) ≤ ((1459854460335407239 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((364963615083851809 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((1957 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-143 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((1957 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-143 / 192 : ℚ) : ℝ) ≤ ((1459854460335407239 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1957 : ((2943254960353643 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((1957 / 64 : ℚ) : ℝ) ∧
    logKernel ((1957 / 64 : ℚ) : ℝ) ≤ ((11773019841414577 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1957
  constructor
  · exact (show ((2943254960353643 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((364963615083851809 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1957 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1459854460335407239 / 18446744073709551616 : ℚ) : ℝ) ≤ ((11773019841414577 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1958 : ((718610757373330867 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((979 / 32 : ℚ) : ℝ) ∧
    heightZ ((979 / 32 : ℚ) : ℝ) ≤ ((1437221514746661737 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((718610757373330867 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((979 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-73 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((979 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-73 / 96 : ℚ) : ℝ) ≤ ((1437221514746661737 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1958 : ((90550750677083 / 562949953421312 : ℚ) : ℝ) ≤ logKernel ((979 / 32 : ℚ) : ℝ) ∧
    logKernel ((979 / 32 : ℚ) : ℝ) ≤ ((11590496086666629 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1958
  constructor
  · exact (show ((90550750677083 / 562949953421312 : ℚ) : ℝ) ≤ zKernel ((718610757373330867 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((979 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1437221514746661737 / 18446744073709551616 : ℚ) : ℝ) ≤ ((11590496086666629 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1959 : ((44216858139237641 / 576460752303423488 : ℚ) : ℝ) ≤ heightZ ((1959 / 64 : ℚ) : ℝ) ∧
    heightZ ((1959 / 64 : ℚ) : ℝ) ≤ ((1414939460455604515 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((44216858139237641 / 576460752303423488 : ℚ) : ℝ) ≤ Real.exp (-((1959 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-149 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((1959 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-149 / 192 : ℚ) : ℝ) ≤ ((1414939460455604515 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1959 : ((11410802100448421 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1959 / 64 : ℚ) : ℝ) ∧
    logKernel ((1959 / 64 : ℚ) : ℝ) ≤ ((5705401050224213 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1959
  constructor
  · exact (show ((11410802100448421 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((44216858139237641 / 576460752303423488 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1959 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1414939460455604515 / 18446744073709551616 : ℚ) : ℝ) ≤ ((5705401050224213 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1960 : ((696501428698448803 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((245 / 8 : ℚ) : ℝ) ∧
    heightZ ((245 / 8 : ℚ) : ℝ) ≤ ((1393002857396897609 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((696501428698448803 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((245 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-19 / 24 : ℚ) : ℝ) ∧
      Real.exp (-((245 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-19 / 24 : ℚ) : ℝ) ≤ ((1393002857396897609 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1960 : ((11233894011265301 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((245 / 8 : ℚ) : ℝ) ∧
    logKernel ((245 / 8 : ℚ) : ℝ) ≤ ((5616947005632653 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1960
  constructor
  · exact (show ((11233894011265301 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((696501428698448803 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((245 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1393002857396897609 / 18446744073709551616 : ℚ) : ℝ) ≤ ((5616947005632653 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1961 : ((1371406349845598713 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1961 / 64 : ℚ) : ℝ) ∧
    heightZ ((1961 / 64 : ℚ) : ℝ) ≤ ((342851587461399679 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((1371406349845598713 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1961 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-155 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((1961 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-155 / 192 : ℚ) : ℝ) ≤ ((342851587461399679 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1961 : ((2764932156946771 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((1961 / 64 : ℚ) : ℝ) ∧
    logKernel ((1961 / 64 : ℚ) : ℝ) ≤ ((11059728627787089 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1961
  constructor
  · exact (show ((2764932156946771 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((1371406349845598713 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1961 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((342851587461399679 / 4611686018427387904 : ℚ) : ℝ) ≤ ((11059728627787089 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1962 : ((1350144665109584555 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((981 / 32 : ℚ) : ℝ) ∧
    heightZ ((981 / 32 : ℚ) : ℝ) ≤ ((675072332554792279 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((1350144665109584555 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((981 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-79 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((981 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-79 / 96 : ℚ) : ℝ) ≤ ((675072332554792279 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1962 : ((10888263428303099 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((981 / 32 : ℚ) : ℝ) ∧
    logKernel ((981 / 32 : ℚ) : ℝ) ≤ ((42532279016809 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1962
  constructor
  · exact (show ((10888263428303099 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((1350144665109584555 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((981 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((675072332554792279 / 9223372036854775808 : ℚ) : ℝ) ≤ ((42532279016809 / 281474976710656 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1963 : ((332303153060561585 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((1963 / 64 : ℚ) : ℝ) ∧
    heightZ ((1963 / 64 : ℚ) : ℝ) ≤ ((1329212612242246343 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((332303153060561585 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((1963 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-161 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((1963 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-161 / 192 : ℚ) : ℝ) ≤ ((1329212612242246343 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1963 : ((5359728275170347 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((1963 / 64 : ℚ) : ℝ) ∧
    logKernel ((1963 / 64 : ℚ) : ℝ) ≤ ((10719456550340699 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1963
  constructor
  · exact (show ((5359728275170347 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((332303153060561585 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1963 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1329212612242246343 / 18446744073709551616 : ℚ) : ℝ) ≤ ((10719456550340699 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1964 : ((81787817548446439 / 1152921504606846976 : ℚ) : ℝ) ≤ heightZ ((491 / 16 : ℚ) : ℝ) ∧
    heightZ ((491 / 16 : ℚ) : ℝ) ≤ ((1308605080775143027 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((81787817548446439 / 1152921504606846976 : ℚ) : ℝ) ≤ Real.exp (-((491 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-41 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((491 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-41 / 48 : ℚ) : ℝ) ≤ ((1308605080775143027 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1964 : ((10553266780444699 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((491 / 16 : ℚ) : ℝ) ∧
    logKernel ((491 / 16 : ℚ) : ℝ) ≤ ((329789586888897 / 2251799813685248 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1964
  constructor
  · exact (show ((10553266780444699 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((81787817548446439 / 1152921504606846976 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((491 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1308605080775143027 / 18446744073709551616 : ℚ) : ℝ) ≤ ((329789586888897 / 2251799813685248 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1965 : ((322079259867575743 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((1965 / 64 : ℚ) : ℝ) ∧
    heightZ ((1965 / 64 : ℚ) : ℝ) ≤ ((1288317039470302975 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((322079259867575743 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((1965 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-167 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((1965 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-167 / 192 : ℚ) : ℝ) ≤ ((1288317039470302975 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1965 : ((649353346507209 / 4503599627370496 : ℚ) : ℝ) ≤ logKernel ((1965 / 64 : ℚ) : ℝ) ∧
    logKernel ((1965 / 64 : ℚ) : ℝ) ≤ ((10389653544115349 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1965
  constructor
  · exact (show ((649353346507209 / 4503599627370496 : ℚ) : ℝ) ≤ zKernel ((322079259867575743 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1965 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1288317039470302975 / 18446744073709551616 : ℚ) : ℝ) ≤ ((10389653544115349 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1966 : ((1268343535091869385 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((983 / 32 : ℚ) : ℝ) ∧
    heightZ ((983 / 32 : ℚ) : ℝ) ≤ ((317085883772967347 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((1268343535091869385 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((983 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-85 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((983 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-85 / 96 : ℚ) : ℝ) ≤ ((317085883772967347 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1966 : ((5114288447951085 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((983 / 32 : ℚ) : ℝ) ∧
    logKernel ((983 / 32 : ℚ) : ℝ) ≤ ((10228576895902175 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1966
  constructor
  · exact (show ((5114288447951085 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((1268343535091869385 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((983 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((317085883772967347 / 4611686018427387904 : ℚ) : ℝ) ≤ ((10228576895902175 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1967 : ((624339845598394797 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((1967 / 64 : ℚ) : ℝ) ∧
    heightZ ((1967 / 64 : ℚ) : ℝ) ≤ ((1248679691196789597 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((624339845598394797 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((1967 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-173 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((1967 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-173 / 192 : ℚ) : ℝ) ≤ ((1248679691196789597 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1967 : ((5034998754825763 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((1967 / 64 : ℚ) : ℝ) ∧
    logKernel ((1967 / 64 : ℚ) : ℝ) ≤ ((10069997509651531 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1967
  constructor
  · exact (show ((5034998754825763 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((624339845598394797 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1967 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1248679691196789597 / 18446744073709551616 : ℚ) : ℝ) ≤ ((10069997509651531 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1968 : ((307330176736063247 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((123 / 4 : ℚ) : ℝ) ∧
    heightZ ((123 / 4 : ℚ) : ℝ) ≤ ((1229320706944252991 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((307330176736063247 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((123 / 4 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-11 / 12 : ℚ) : ℝ) ∧
      Real.exp (-((123 / 4 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-11 / 12 : ℚ) : ℝ) ≤ ((1229320706944252991 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1968 : ((619617291806579 / 4503599627370496 : ℚ) : ℝ) ≤ logKernel ((123 / 4 : ℚ) : ℝ) ∧
    logKernel ((123 / 4 : ℚ) : ℝ) ≤ ((9913876668905269 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1968
  constructor
  · exact (show ((619617291806579 / 4503599627370496 : ℚ) : ℝ) ≤ zKernel ((307330176736063247 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((123 / 4 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1229320706944252991 / 18446744073709551616 : ℚ) : ℝ) ≤ ((9913876668905269 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

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

theorem log_height_bounds_96 : ((15359655823398785 / 4503599627370496 : ℚ) : ℝ) ≤ Real.log ((969 / 32 : ℚ) : ℝ) ∧
    Real.log ((969 / 32 : ℚ) : ℝ) ≤ ((245754493174380563 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((15359655823398785 / 4503599627370496 : ℚ) : ℝ) ≤ ((969 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((969 / 32 : ℚ) : ℝ) ≤ Real.exp ((245754493174380563 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_96 : heightPower (96 : Fin 988) ≤ ((218305477070525 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_96
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_96 : heightFactor (96 : Fin 988) ≤ ((1498637345146289 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_96
  obtain ⟨hpl, hph⟩ := kernel_bounds_1937
  obtain ⟨hcl, hch⟩ := kernel_bounds_1938
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1938
  have h : (((938961 / 512 : ℚ) : ℝ) * (logKernel ((1937 / 64 : ℚ) : ℝ) - logKernel ((969 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((969 / 32 : ℚ) : ℝ) + Real.log ((969 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1498637345146289 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_97 : ((245791665006021463 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1939 / 64 : ℚ) : ℝ) ∧
    Real.log ((1939 / 64 : ℚ) : ℝ) ≤ ((122895832503010733 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((245791665006021463 / 72057594037927936 : ℚ) : ℝ) ≤ ((1939 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1939 / 64 : ℚ) : ℝ) ≤ Real.exp ((122895832503010733 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_97 : heightPower (97 : Fin 988) ≤ ((441154203119501 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_97
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_97 : heightFactor (97 : Fin 988) ≤ ((742446912841387 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_97
  obtain ⟨hpl, hph⟩ := kernel_bounds_1938
  obtain ⟨hcl, hch⟩ := kernel_bounds_1939
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1939
  have h : (((3759721 / 2048 : ℚ) : ℝ) * (logKernel ((969 / 32 : ℚ) : ℝ) - logKernel ((1939 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1939 / 64 : ℚ) : ℝ) + Real.log ((1939 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((742446912841387 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_98 : ((245828817671983951 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((485 / 16 : ℚ) : ℝ) ∧
    Real.log ((485 / 16 : ℚ) : ℝ) ≤ ((122914408835991977 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((245828817671983951 / 72057594037927936 : ℚ) : ℝ) ≤ ((485 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((485 / 16 : ℚ) : ℝ) ≤ Real.exp ((122914408835991977 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_98 : heightPower (98 : Fin 988) ≤ ((445697377232021 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_98
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_98 : heightFactor (98 : Fin 988) ≤ ((1471275430507367 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_98
  obtain ⟨hpl, hph⟩ := kernel_bounds_1939
  obtain ⟨hcl, hch⟩ := kernel_bounds_1940
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1940
  have h : (((235225 / 128 : ℚ) : ℝ) * (logKernel ((1939 / 64 : ℚ) : ℝ) - logKernel ((485 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((485 / 16 : ℚ) : ℝ) + Real.log ((485 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1471275430507367 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_99 : ((245865951192021363 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1941 / 64 : ℚ) : ℝ) ∧
    Real.log ((1941 / 64 : ℚ) : ℝ) ≤ ((122932975596010683 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((245865951192021363 / 72057594037927936 : ℚ) : ℝ) ≤ ((1941 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1941 / 64 : ℚ) : ℝ) ≤ Real.exp ((122932975596010683 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_99 : heightPower (99 : Fin 988) ≤ ((450240476555771 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_99
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_99 : heightFactor (99 : Fin 988) ≤ ((1457781029827119 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_99
  obtain ⟨hpl, hph⟩ := kernel_bounds_1940
  obtain ⟨hcl, hch⟩ := kernel_bounds_1941
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1941
  have h : (((3767481 / 2048 : ℚ) : ℝ) * (logKernel ((485 / 16 : ℚ) : ℝ) - logKernel ((1941 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1941 / 64 : ℚ) : ℝ) + Real.log ((1941 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1457781029827119 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_100 : ((30737883198232065 / 9007199254740992 : ℚ) : ℝ) ≤ Real.log ((971 / 32 : ℚ) : ℝ) ∧
    Real.log ((971 / 32 : ℚ) : ℝ) ≤ ((245903065585856523 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((30737883198232065 / 9007199254740992 : ℚ) : ℝ) ≤ ((971 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((971 / 32 : ℚ) : ℝ) ≤ Real.exp ((245903065585856523 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_100 : heightPower (100 : Fin 988) ≤ ((227391750583897 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_100
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_100 : heightFactor (100 : Fin 988) ≤ ((722204751977103 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_100
  obtain ⟨hpl, hph⟩ := kernel_bounds_1941
  obtain ⟨hcl, hch⟩ := kernel_bounds_1942
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1942
  have h : (((942841 / 512 : ℚ) : ℝ) * (logKernel ((1941 / 64 : ℚ) : ℝ) - logKernel ((971 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((971 / 32 : ℚ) : ℝ) + Real.log ((971 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((722204751977103 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_101 : ((61485040218295445 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((1943 / 64 : ℚ) : ℝ) ∧
    Real.log ((1943 / 64 : ℚ) : ℝ) ≤ ((245940160873181783 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((61485040218295445 / 18014398509481984 : ℚ) : ℝ) ≤ ((1943 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1943 / 64 : ℚ) : ℝ) ≤ Real.exp ((245940160873181783 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_101 : heightPower (101 : Fin 988) ≤ ((114831612786253 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_101
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_101 : heightFactor (101 : Fin 988) ≤ ((2862319486433065 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_101
  obtain ⟨hpl, hph⟩ := kernel_bounds_1942
  obtain ⟨hcl, hch⟩ := kernel_bounds_1943
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1943
  have h : (((3775249 / 2048 : ℚ) : ℝ) * (logKernel ((971 / 32 : ℚ) : ℝ) - logKernel ((1943 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1943 / 64 : ℚ) : ℝ) + Real.log ((1943 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((2862319486433065 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_102 : ((245977237073659105 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((243 / 8 : ℚ) : ℝ) ∧
    Real.log ((243 / 8 : ℚ) : ℝ) ≤ ((61494309268414777 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((245977237073659105 / 72057594037927936 : ℚ) : ℝ) ≤ ((243 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((243 / 8 : ℚ) : ℝ) ≤ Real.exp ((61494309268414777 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_102 : heightPower (102 : Fin 988) ≤ ((231934663282115 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_102
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_102 : heightFactor (102 : Fin 988) ≤ ((2836061295738243 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_102
  obtain ⟨hpl, hph⟩ := kernel_bounds_1943
  obtain ⟨hcl, hch⟩ := kernel_bounds_1944
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1944
  have h : (((59049 / 32 : ℚ) : ℝ) * (logKernel ((1943 / 64 : ℚ) : ℝ) - logKernel ((243 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((243 / 8 : ℚ) : ℝ) + Real.log ((243 / 8 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((2836061295738243 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_103 : ((246014294206920121 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1945 / 64 : ℚ) : ℝ) ∧
    Real.log ((1945 / 64 : ℚ) : ℝ) ≤ ((61503573551730031 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((246014294206920121 / 72057594037927936 : ℚ) : ℝ) ≤ ((1945 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1945 / 64 : ℚ) : ℝ) ≤ Real.exp ((61503573551730031 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_103 : heightPower (103 : Fin 988) ≤ ((468412127502135 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_103
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_103 : heightFactor (103 : Fin 988) ≤ ((10976727562549 / 1099511627776 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_103
  obtain ⟨hpl, hph⟩ := kernel_bounds_1944
  obtain ⟨hcl, hch⟩ := kernel_bounds_1945
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1945
  have h : (((3783025 / 2048 : ℚ) : ℝ) * (logKernel ((243 / 8 : ℚ) : ℝ) - logKernel ((1945 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1945 / 64 : ℚ) : ℝ) + Real.log ((1945 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((10976727562549 / 1099511627776 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_104 : ((246051332292566183 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((973 / 32 : ℚ) : ℝ) ∧
    Real.log ((973 / 32 : ℚ) : ℝ) ≤ ((123025666146283093 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((246051332292566183 / 72057594037927936 : ℚ) : ℝ) ≤ ((973 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((973 / 32 : ℚ) : ℝ) ≤ Real.exp ((123025666146283093 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_104 : heightPower (104 : Fin 988) ≤ ((236477427017647 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_104
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_104 : heightFactor (104 : Fin 988) ≤ ((2784260206948975 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_104
  obtain ⟨hpl, hph⟩ := kernel_bounds_1945
  obtain ⟨hcl, hch⟩ := kernel_bounds_1946
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1946
  have h : (((946729 / 512 : ℚ) : ℝ) * (logKernel ((1945 / 64 : ℚ) : ℝ) - logKernel ((973 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((973 / 32 : ℚ) : ℝ) + Real.log ((973 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((2784260206948975 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_105 : ((246088351350168435 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1947 / 64 : ℚ) : ℝ) ∧
    Real.log ((1947 / 64 : ℚ) : ℝ) ≤ ((123044175675084219 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((246088351350168435 / 72057594037927936 : ℚ) : ℝ) ≤ ((1947 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1947 / 64 : ℚ) : ℝ) ≤ Real.exp ((123044175675084219 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_105 : heightPower (105 : Fin 988) ≤ ((477497506240157 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_105
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_105 : heightFactor (105 : Fin 988) ≤ ((172419562973271 / 17592186044416 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_105
  obtain ⟨hpl, hph⟩ := kernel_bounds_1946
  obtain ⟨hcl, hch⟩ := kernel_bounds_1947
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1947
  have h : (((3790809 / 2048 : ℚ) : ℝ) * (logKernel ((973 / 32 : ℚ) : ℝ) - logKernel ((1947 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1947 / 64 : ℚ) : ℝ) + Real.log ((1947 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((172419562973271 / 17592186044416 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_106 : ((246125351399267873 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((487 / 16 : ℚ) : ℝ) ∧
    Real.log ((487 / 16 : ℚ) : ℝ) ≤ ((61531337849816969 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((246125351399267873 / 72057594037927936 : ℚ) : ℝ) ≤ ((487 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((487 / 16 : ℚ) : ℝ) ≤ Real.exp ((61531337849816969 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_106 : heightPower (106 : Fin 988) ≤ ((15063752631033 / 8796093022208 : ℚ) : ℝ) := by
  have hh := log_height_bounds_106
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_106 : heightFactor (106 : Fin 988) ≤ ((1366699268034047 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_106
  obtain ⟨hpl, hph⟩ := kernel_bounds_1947
  obtain ⟨hcl, hch⟩ := kernel_bounds_1948
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1948
  have h : (((237169 / 128 : ℚ) : ℝ) * (logKernel ((1947 / 64 : ℚ) : ℝ) - logKernel ((487 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((487 / 16 : ℚ) : ℝ) + Real.log ((487 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1366699268034047 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_107 : ((15385145778710963 / 4503599627370496 : ℚ) : ℝ) ≤ Real.log ((1949 / 64 : ℚ) : ℝ) ∧
    Real.log ((1949 / 64 : ℚ) : ℝ) ≤ ((246162332459375411 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((15385145778710963 / 4503599627370496 : ℚ) : ℝ) ≤ ((1949 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1949 / 64 : ℚ) : ℝ) ≤ Real.exp ((246162332459375411 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_107 : heightPower (107 : Fin 988) ≤ ((486582587970205 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_107
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_107 : heightFactor (107 : Fin 988) ≤ ((338539336201597 / 35184372088832 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_107
  obtain ⟨hpl, hph⟩ := kernel_bounds_1948
  obtain ⟨hcl, hch⟩ := kernel_bounds_1949
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1949
  have h : (((3798601 / 2048 : ℚ) : ℝ) * (logKernel ((487 / 16 : ℚ) : ℝ) - logKernel ((1949 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1949 / 64 : ℚ) : ℝ) + Real.log ((1949 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((338539336201597 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_108 : ((246199294549971925 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((975 / 32 : ℚ) : ℝ) ∧
    Real.log ((975 / 32 : ℚ) : ℝ) ≤ ((30774911818746491 / 9007199254740992 : ℚ) : ℝ) := by
  have hl : Real.exp ((246199294549971925 / 72057594037927936 : ℚ) : ℝ) ≤ ((975 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((975 / 32 : ℚ) : ℝ) ≤ Real.exp ((30774911818746491 / 9007199254740992 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_108 : heightPower (108 : Fin 988) ≤ ((491125017647701 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_108
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_108 : heightFactor (108 : Fin 988) ≤ ((2683459384205823 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_108
  obtain ⟨hpl, hph⟩ := kernel_bounds_1949
  obtain ⟨hcl, hch⟩ := kernel_bounds_1950
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1950
  have h : (((950625 / 512 : ℚ) : ℝ) * (logKernel ((1949 / 64 : ℚ) : ℝ) - logKernel ((975 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((975 / 32 : ℚ) : ℝ) + Real.log ((975 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((2683459384205823 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_109 : ((123118118845254173 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((1951 / 64 : ℚ) : ℝ) ∧
    Real.log ((1951 / 64 : ℚ) : ℝ) ≤ ((246236237690508349 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((123118118845254173 / 36028797018963968 : ℚ) : ℝ) ≤ ((1951 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1951 / 64 : ℚ) : ℝ) ≤ Real.exp ((246236237690508349 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_109 : heightPower (109 : Fin 988) ≤ ((247833686650763 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_109
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_109 : heightFactor (109 : Fin 988) ≤ ((1329415277251463 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_109
  obtain ⟨hpl, hph⟩ := kernel_bounds_1950
  obtain ⟨hcl, hch⟩ := kernel_bounds_1951
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1951
  have h : (((3806401 / 2048 : ℚ) : ℝ) * (logKernel ((975 / 32 : ℚ) : ℝ) - logKernel ((1951 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1951 / 64 : ℚ) : ℝ) + Real.log ((1951 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1329415277251463 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_110 : ((246273161900405693 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((61 / 2 : ℚ) : ℝ) ∧
    Real.log ((61 / 2 : ℚ) : ℝ) ≤ ((3848018154693839 / 1125899906842624 : ℚ) : ℝ) := by
  have hl : Real.exp ((246273161900405693 / 72057594037927936 : ℚ) : ℝ) ≤ ((61 / 2 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((61 / 2 : ℚ) : ℝ) ≤ Real.exp ((3848018154693839 / 1125899906842624 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_110 : heightPower (110 : Fin 988) ≤ ((500209655007541 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_110
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_110 : heightFactor (110 : Fin 988) ≤ ((658606538412705 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_110
  obtain ⟨hpl, hph⟩ := kernel_bounds_1951
  obtain ⟨hcl, hch⟩ := kernel_bounds_1952
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1952
  have h : (((3721 / 2 : ℚ) : ℝ) * (logKernel ((1951 / 64 : ℚ) : ℝ) - logKernel ((61 / 2 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((61 / 2 : ℚ) : ℝ) + Real.log ((61 / 2 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((658606538412705 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_111 : ((246310067199055147 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1953 / 64 : ℚ) : ℝ) ∧
    Real.log ((1953 / 64 : ℚ) : ℝ) ≤ ((123155033599527575 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((246310067199055147 / 72057594037927936 : ℚ) : ℝ) ≤ ((1953 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1953 / 64 : ℚ) : ℝ) ≤ Real.exp ((123155033599527575 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_111 : heightPower (111 : Fin 988) ≤ ((504751862841495 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_111
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_111 : heightFactor (111 : Fin 988) ≤ ((2610244153123509 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_111
  obtain ⟨hpl, hph⟩ := kernel_bounds_1952
  obtain ⟨hcl, hch⟩ := kernel_bounds_1953
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1953
  have h : (((3814209 / 2048 : ℚ) : ℝ) * (logKernel ((61 / 2 : ℚ) : ℝ) - logKernel ((1953 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1953 / 64 : ℚ) : ℝ) + Real.log ((1953 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((2610244153123509 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_112 : ((246346953605818109 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((977 / 32 : ℚ) : ℝ) ∧
    Real.log ((977 / 32 : ℚ) : ℝ) ≤ ((962292787522727 / 281474976710656 : ℚ) : ℝ) := by
  have hl : Real.exp ((246346953605818109 / 72057594037927936 : ℚ) : ℝ) ≤ ((977 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((977 / 32 : ℚ) : ℝ) ≤ Real.exp ((962292787522727 / 281474976710656 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_112 : heightPower (112 : Fin 988) ≤ ((63661749609877 / 35184372088832 : ℚ) : ℝ) := by
  have hh := log_height_bounds_112
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_112 : heightFactor (112 : Fin 988) ≤ ((1293141271279971 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_112
  obtain ⟨hpl, hph⟩ := kernel_bounds_1953
  obtain ⟨hcl, hch⟩ := kernel_bounds_1954
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1954
  have h : (((954529 / 512 : ℚ) : ℝ) * (logKernel ((1953 / 64 : ℚ) : ℝ) - logKernel ((977 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((977 / 32 : ℚ) : ℝ) + Real.log ((977 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1293141271279971 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_113 : ((123191910570013131 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((1955 / 64 : ℚ) : ℝ) ∧
    Real.log ((1955 / 64 : ℚ) : ℝ) ≤ ((246383821140026265 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((123191910570013131 / 36028797018963968 : ℚ) : ℝ) ≤ ((1955 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1955 / 64 : ℚ) : ℝ) ≤ Real.exp ((246383821140026265 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_113 : heightPower (113 : Fin 988) ≤ ((513836057195621 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_113
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_113 : heightFactor (113 : Fin 988) ≤ ((2562539329603093 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_113
  obtain ⟨hpl, hph⟩ := kernel_bounds_1954
  obtain ⟨hcl, hch⟩ := kernel_bounds_1955
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1955
  have h : (((3822025 / 2048 : ℚ) : ℝ) * (logKernel ((977 / 32 : ℚ) : ℝ) - logKernel ((1955 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1955 / 64 : ℚ) : ℝ) + Real.log ((1955 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((2562539329603093 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_114 : ((123210334910490817 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((489 / 16 : ℚ) : ℝ) ∧
    Real.log ((489 / 16 : ℚ) : ℝ) ≤ ((246420669820981637 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((123210334910490817 / 36028797018963968 : ℚ) : ℝ) ≤ ((489 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((489 / 16 : ℚ) : ℝ) ≤ Real.exp ((246420669820981637 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_114 : heightPower (114 : Fin 988) ≤ ((518378043866707 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_114
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_114 : heightFactor (114 : Fin 988) ≤ ((2539012539740457 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_114
  obtain ⟨hpl, hph⟩ := kernel_bounds_1955
  obtain ⟨hcl, hch⟩ := kernel_bounds_1956
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1956
  have h : (((239121 / 128 : ℚ) : ℝ) * (logKernel ((1955 / 64 : ℚ) : ℝ) - logKernel ((489 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((489 / 16 : ℚ) : ℝ) + Real.log ((489 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((2539012539740457 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_115 : ((61614374916989163 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((1957 / 64 : ℚ) : ℝ) ∧
    Real.log ((1957 / 64 : ℚ) : ℝ) ≤ ((246457499667956655 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((61614374916989163 / 18014398509481984 : ℚ) : ℝ) ≤ ((1957 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1957 / 64 : ℚ) : ℝ) ≤ Real.exp ((246457499667956655 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_115 : heightPower (115 : Fin 988) ≤ ((522919956967557 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_115
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_115 : heightFactor (115 : Fin 988) ≤ ((1257850108072969 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_115
  obtain ⟨hpl, hph⟩ := kernel_bounds_1956
  obtain ⟨hcl, hch⟩ := kernel_bounds_1957
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1957
  have h : (((3829849 / 2048 : ℚ) : ℝ) * (logKernel ((489 / 16 : ℚ) : ℝ) - logKernel ((1957 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1957 / 64 : ℚ) : ℝ) + Real.log ((1957 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1257850108072969 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_116 : ((246494310700194211 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((979 / 32 : ℚ) : ℝ) ∧
    Real.log ((979 / 32 : ℚ) : ℝ) ≤ ((123247155350097107 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((246494310700194211 / 72057594037927936 : ℚ) : ℝ) ≤ ((979 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((979 / 32 : ℚ) : ℝ) ≤ Real.exp ((123247155350097107 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_116 : heightPower (116 : Fin 988) ≤ ((527461796573339 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_116
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_116 : heightFactor (116 : Fin 988) ≤ ((1246300209761561 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_116
  obtain ⟨hpl, hph⟩ := kernel_bounds_1957
  obtain ⟨hcl, hch⟩ := kernel_bounds_1958
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1958
  have h : (((958441 / 512 : ℚ) : ℝ) * (logKernel ((1957 / 64 : ℚ) : ℝ) - logKernel ((979 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((979 / 32 : ℚ) : ℝ) + Real.log ((979 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1246300209761561 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_117 : ((15408193933556733 / 4503599627370496 : ℚ) : ℝ) ≤ Real.log ((1959 / 64 : ℚ) : ℝ) ∧
    Real.log ((1959 / 64 : ℚ) : ℝ) ≤ ((246531102936907731 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((15408193933556733 / 4503599627370496 : ℚ) : ℝ) ≤ ((1959 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1959 / 64 : ℚ) : ℝ) ≤ Real.exp ((246531102936907731 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_117 : heightPower (117 : Fin 988) ≤ ((532003562759105 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_117
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_117 : heightFactor (117 : Fin 988) ≤ ((2469711227949917 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_117
  obtain ⟨hpl, hph⟩ := kernel_bounds_1958
  obtain ⟨hcl, hch⟩ := kernel_bounds_1959
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1959
  have h : (((3837681 / 2048 : ℚ) : ℝ) * (logKernel ((979 / 32 : ℚ) : ℝ) - logKernel ((1959 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1959 / 64 : ℚ) : ℝ) + Real.log ((1959 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((2469711227949917 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_118 : ((246567876397281203 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((245 / 8 : ℚ) : ℝ) ∧
    Real.log ((245 / 8 : ℚ) : ℝ) ≤ ((123283938198640603 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((246567876397281203 / 72057594037927936 : ℚ) : ℝ) ≤ ((245 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((245 / 8 : ℚ) : ℝ) ≤ Real.exp ((123283938198640603 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_118 : heightPower (118 : Fin 988) ≤ ((536545255599793 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_118
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_118 : heightFactor (118 : Fin 988) ≤ ((2447030736724563 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_118
  obtain ⟨hpl, hph⟩ := kernel_bounds_1959
  obtain ⟨hcl, hch⟩ := kernel_bounds_1960
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1960
  have h : (((60025 / 32 : ℚ) : ℝ) * (logKernel ((1959 / 64 : ℚ) : ℝ) - logKernel ((245 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((245 / 8 : ℚ) : ℝ) + Real.log ((245 / 8 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((2447030736724563 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_119 : ((123302315550234641 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((1961 / 64 : ℚ) : ℝ) ∧
    Real.log ((1961 / 64 : ℚ) : ℝ) ≤ ((246604631100469285 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((123302315550234641 / 36028797018963968 : ℚ) : ℝ) ≤ ((1961 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1961 / 64 : ℚ) : ℝ) ≤ Real.exp ((246604631100469285 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_119 : heightPower (119 : Fin 988) ≤ ((270543437585113 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_119
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_119 : heightFactor (119 : Fin 988) ≤ ((151534816138311 / 17592186044416 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_119
  obtain ⟨hpl, hph⟩ := kernel_bounds_1960
  obtain ⟨hcl, hch⟩ := kernel_bounds_1961
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1961
  have h : (((3845521 / 2048 : ℚ) : ℝ) * (logKernel ((245 / 8 : ℚ) : ℝ) - logKernel ((1961 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1961 / 64 : ℚ) : ℝ) + Real.log ((1961 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((151534816138311 / 17592186044416 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_120 : ((246641367065597315 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((981 / 32 : ℚ) : ℝ) ∧
    Real.log ((981 / 32 : ℚ) : ℝ) ≤ ((123320683532798659 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((246641367065597315 / 72057594037927936 : ℚ) : ℝ) ≤ ((981 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((981 / 32 : ℚ) : ℝ) ≤ Real.exp ((123320683532798659 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_120 : heightPower (120 : Fin 988) ≤ ((545628421545111 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_120
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_120 : heightFactor (120 : Fin 988) ≤ ((2402288321697439 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_120
  obtain ⟨hpl, hph⟩ := kernel_bounds_1961
  obtain ⟨hcl, hch⟩ := kernel_bounds_1962
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1962
  have h : (((962361 / 512 : ℚ) : ℝ) * (logKernel ((1961 / 64 : ℚ) : ℝ) - logKernel ((981 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((981 / 32 : ℚ) : ℝ) + Real.log ((981 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((2402288321697439 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_121 : ((246678084311761415 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1963 / 64 : ℚ) : ℝ) ∧
    Real.log ((1963 / 64 : ℚ) : ℝ) ≤ ((123339042155880709 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((246678084311761415 / 72057594037927936 : ℚ) : ℝ) ≤ ((1963 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1963 / 64 : ℚ) : ℝ) ≤ Real.exp ((123339042155880709 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_121 : heightPower (121 : Fin 988) ≤ ((137542473699761 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_121
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_121 : heightFactor (121 : Fin 988) ≤ ((2380222673226611 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_121
  obtain ⟨hpl, hph⟩ := kernel_bounds_1962
  obtain ⟨hcl, hch⟩ := kernel_bounds_1963
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1963
  have h : (((3853369 / 2048 : ℚ) : ℝ) * (logKernel ((981 / 32 : ℚ) : ℝ) - logKernel ((1963 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1963 / 64 : ℚ) : ℝ) + Real.log ((1963 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((2380222673226611 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_122 : ((246714782858028519 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((491 / 16 : ℚ) : ℝ) ∧
    Real.log ((491 / 16 : ℚ) : ℝ) ≤ ((123357391429014261 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((246714782858028519 / 72057594037927936 : ℚ) : ℝ) ≤ ((491 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((491 / 16 : ℚ) : ℝ) ≤ Real.exp ((123357391429014261 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_122 : heightPower (122 : Fin 988) ≤ ((554711295006503 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_122
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_122 : heightFactor (122 : Fin 988) ≤ ((1179179137733429 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_122
  obtain ⟨hpl, hph⟩ := kernel_bounds_1963
  obtain ⟨hcl, hch⟩ := kernel_bounds_1964
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1964
  have h : (((241081 / 128 : ℚ) : ℝ) * (logKernel ((1963 / 64 : ℚ) : ℝ) - logKernel ((491 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((491 / 16 : ℚ) : ℝ) + Real.log ((491 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1179179137733429 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_123 : ((246751462723436447 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1965 / 64 : ℚ) : ℝ) ∧
    Real.log ((1965 / 64 : ℚ) : ℝ) ≤ ((123375731361718225 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((246751462723436447 / 72057594037927936 : ℚ) : ℝ) ≤ ((1965 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1965 / 64 : ℚ) : ℝ) ≤ Real.exp ((123375731361718225 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_123 : heightPower (123 : Fin 988) ≤ ((559252622241857 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_123
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_123 : heightFactor (123 : Fin 988) ≤ ((292086663444359 / 35184372088832 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_123
  obtain ⟨hpl, hph⟩ := kernel_bounds_1964
  obtain ⟨hcl, hch⟩ := kernel_bounds_1965
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1965
  have h : (((3861225 / 2048 : ℚ) : ℝ) * (logKernel ((491 / 16 : ℚ) : ℝ) - logKernel ((1965 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1965 / 64 : ℚ) : ℝ) + Real.log ((1965 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((292086663444359 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_124 : ((30848515490874245 / 9007199254740992 : ℚ) : ℝ) ≤ Real.log ((983 / 32 : ℚ) : ℝ) ∧
    Real.log ((983 / 32 : ℚ) : ℝ) ≤ ((246788123926993963 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((30848515490874245 / 9007199254740992 : ℚ) : ℝ) ≤ ((983 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((983 / 32 : ℚ) : ℝ) ≤ Real.exp ((246788123926993963 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_124 : heightPower (124 : Fin 988) ≤ ((281896938289679 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_124
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_124 : heightFactor (124 : Fin 988) ≤ ((578806491237899 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_124
  obtain ⟨hpl, hph⟩ := kernel_bounds_1965
  obtain ⟨hcl, hch⟩ := kernel_bounds_1966
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1966
  have h : (((966289 / 512 : ℚ) : ℝ) * (logKernel ((1965 / 64 : ℚ) : ℝ) - logKernel ((983 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((983 / 32 : ℚ) : ℝ) + Real.log ((983 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((578806491237899 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_125 : ((61706191621920205 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((1967 / 64 : ℚ) : ℝ) ∧
    Real.log ((1967 / 64 : ℚ) : ℝ) ≤ ((246824766487680823 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((61706191621920205 / 18014398509481984 : ℚ) : ℝ) ≤ ((1967 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1967 / 64 : ℚ) : ℝ) ≤ Real.exp ((246824766487680823 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_125 : heightPower (125 : Fin 988) ≤ ((568335058093145 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_125
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_125 : heightFactor (125 : Fin 988) ≤ ((286744307412177 / 35184372088832 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_125
  obtain ⟨hpl, hph⟩ := kernel_bounds_1966
  obtain ⟨hcl, hch⟩ := kernel_bounds_1967
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1967
  have h : (((3869089 / 2048 : ℚ) : ℝ) * (logKernel ((983 / 32 : ℚ) : ℝ) - logKernel ((1967 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1967 / 64 : ℚ) : ℝ) + Real.log ((1967 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((286744307412177 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_126 : ((123430695212223925 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((123 / 4 : ℚ) : ℝ) ∧
    Real.log ((123 / 4 : ℚ) : ℝ) ≤ ((246861390424447853 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((123430695212223925 / 36028797018963968 : ℚ) : ℝ) ≤ ((123 / 4 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((123 / 4 : ℚ) : ℝ) ≤ Real.exp ((246861390424447853 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_126 : heightPower (126 : Fin 988) ≤ ((572876166857245 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_126
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_126 : heightFactor (126 : Fin 988) ≤ ((1136438509134315 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_126
  obtain ⟨hpl, hph⟩ := kernel_bounds_1967
  obtain ⟨hcl, hch⟩ := kernel_bounds_1968
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1968
  have h : (((15129 / 8 : ℚ) : ℝ) * (logKernel ((1967 / 64 : ℚ) : ℝ) - logKernel ((123 / 4 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((123 / 4 : ℚ) : ℝ) + Real.log ((123 / 4 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1136438509134315 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_127 : ((7715562367381781 / 2251799813685248 : ℚ) : ℝ) ≤ Real.log ((1969 / 64 : ℚ) : ℝ) ∧
    Real.log ((1969 / 64 : ℚ) : ℝ) ≤ ((246897995756216995 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((7715562367381781 / 2251799813685248 : ℚ) : ℝ) ≤ ((1969 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1969 / 64 : ℚ) : ℝ) ≤ Real.exp ((246897995756216995 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_127 : heightPower (127 : Fin 988) ≤ ((144354300736393 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_127
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_127 : heightFactor (127 : Fin 988) ≤ ((2251991885435173 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_127
  obtain ⟨hpl, hph⟩ := kernel_bounds_1968
  obtain ⟨hcl, hch⟩ := kernel_bounds_1969
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1969
  have h : (((3876961 / 2048 : ℚ) : ℝ) * (logKernel ((123 / 4 : ℚ) : ℝ) - logKernel ((1969 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1969 / 64 : ℚ) : ℝ) + Real.log ((1969 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((2251991885435173 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

end LegendreK6.M2Pilot.Enclosures.Height003
