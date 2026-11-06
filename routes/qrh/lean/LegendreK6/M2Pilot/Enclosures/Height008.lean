import LegendreK6.M2PilotDefinitions
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp

/-! Generated proposals: every bound is checked by Lean, not by trusting Arb. -/
namespace LegendreK6.M2Pilot.Enclosures.Height008
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem height_z_bounds_2097 : ((40947782765471793 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((2097 / 64 : ℚ) : ℝ) ∧
    heightZ ((2097 / 64 : ℚ) : ℝ) ≤ ((163791131061887175 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((40947782765471793 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((2097 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-563 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2097 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-563 / 192 : ℚ) : ℝ) ≤ ((163791131061887175 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2097 : ((750618614490475 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2097 / 64 : ℚ) : ℝ) ∧
    logKernel ((2097 / 64 : ℚ) : ℝ) ≤ ((46913663405655 / 4503599627370496 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2097
  constructor
  · exact (show ((750618614490475 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((40947782765471793 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2097 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((163791131061887175 / 18446744073709551616 : ℚ) : ℝ) ≤ ((46913663405655 / 4503599627370496 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2098 : ((161251784943513797 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1049 / 32 : ℚ) : ℝ) ∧
    heightZ ((1049 / 32 : ℚ) : ℝ) ≤ ((20156473117939225 / 2305843009213693952 : ℚ) : ℝ) := by
  have h : ((161251784943513797 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1049 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-283 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1049 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-283 / 96 : ℚ) : ℝ) ≤ ((20156473117939225 / 2305843009213693952 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2098 : ((727524507580755 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1049 / 32 : ℚ) : ℝ) ∧
    logKernel ((1049 / 32 : ℚ) : ℝ) ≤ ((90940563447595 / 9007199254740992 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2098
  constructor
  · exact (show ((727524507580755 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((161251784943513797 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1049 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((20156473117939225 / 2305843009213693952 : ℚ) : ℝ) ≤ ((90940563447595 / 9007199254740992 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2099 : ((79375903868825847 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2099 / 64 : ℚ) : ℝ) ∧
    heightZ ((2099 / 64 : ℚ) : ℝ) ≤ ((158751807737651697 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((79375903868825847 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2099 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-569 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2099 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-569 / 192 : ℚ) : ℝ) ≤ ((158751807737651697 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2099 : ((88142616455413 / 9007199254740992 : ℚ) : ℝ) ≤ logKernel ((2099 / 64 : ℚ) : ℝ) ∧
    logKernel ((2099 / 64 : ℚ) : ℝ) ≤ ((705140931643309 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2099
  constructor
  · exact (show ((88142616455413 / 9007199254740992 : ℚ) : ℝ) ≤ zKernel ((79375903868825847 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2099 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((158751807737651697 / 18446744073709551616 : ℚ) : ℝ) ≤ ((705140931643309 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2100 : ((78145294542942859 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((525 / 16 : ℚ) : ℝ) ∧
    heightZ ((525 / 16 : ℚ) : ℝ) ≤ ((156290589085885721 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((78145294542942859 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((525 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-143 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((525 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-143 / 48 : ℚ) : ℝ) ≤ ((156290589085885721 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2100 : ((341723012969151 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((525 / 16 : ℚ) : ℝ) ∧
    logKernel ((525 / 16 : ℚ) : ℝ) ≤ ((683446025938307 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2100
  constructor
  · exact (show ((341723012969151 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((78145294542942859 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((525 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((156290589085885721 / 18446744073709551616 : ℚ) : ℝ) ≤ ((683446025938307 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2101 : ((153867528092530859 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2101 / 64 : ℚ) : ℝ) ∧
    heightZ ((2101 / 64 : ℚ) : ℝ) ≤ ((76933764046265431 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((153867528092530859 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2101 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-575 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2101 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-575 / 192 : ℚ) : ℝ) ≤ ((76933764046265431 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2101 : ((82802325288773 / 9007199254740992 : ℚ) : ℝ) ≤ logKernel ((2101 / 64 : ℚ) : ℝ) ∧
    logKernel ((2101 / 64 : ℚ) : ℝ) ≤ ((662418602310189 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2101
  constructor
  · exact (show ((82802325288773 / 9007199254740992 : ℚ) : ℝ) ≤ zKernel ((153867528092530859 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2101 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((76933764046265431 / 9223372036854775808 : ℚ) : ℝ) ≤ ((662418602310189 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2102 : ((151482033177926215 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1051 / 32 : ℚ) : ℝ) ∧
    heightZ ((1051 / 32 : ℚ) : ℝ) ≤ ((75741016588963109 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((151482033177926215 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1051 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-289 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1051 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-289 / 96 : ℚ) : ℝ) ≤ ((75741016588963109 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2102 : ((642038124494399 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1051 / 32 : ℚ) : ℝ) ∧
    logKernel ((1051 / 32 : ℚ) : ℝ) ≤ ((160509531123601 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2102
  constructor
  · exact (show ((642038124494399 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((151482033177926215 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1051 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((75741016588963109 / 9223372036854775808 : ℚ) : ℝ) ≤ ((160509531123601 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2103 : ((74566760967001711 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2103 / 64 : ℚ) : ℝ) ∧
    heightZ ((2103 / 64 : ℚ) : ℝ) ≤ ((149133521934003425 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((74566760967001711 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2103 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-581 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2103 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-581 / 192 : ℚ) : ℝ) ≤ ((149133521934003425 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2103 : ((19446396501901 / 2251799813685248 : ℚ) : ℝ) ≤ logKernel ((2103 / 64 : ℚ) : ℝ) ∧
    logKernel ((2103 / 64 : ℚ) : ℝ) ≤ ((622284688060837 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2103
  constructor
  · exact (show ((19446396501901 / 2251799813685248 : ℚ) : ℝ) ≤ zKernel ((74566760967001711 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2103 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((149133521934003425 / 18446744073709551616 : ℚ) : ℝ) ≤ ((622284688060837 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2104 : ((146821420982094293 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((263 / 8 : ℚ) : ℝ) ∧
    heightZ ((263 / 8 : ℚ) : ℝ) ≤ ((18352677622761787 / 2305843009213693952 : ℚ) : ℝ) := by
  have h : ((146821420982094293 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((263 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-73 / 24 : ℚ) : ℝ) ∧
      Real.exp (-((263 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-73 / 24 : ℚ) : ℝ) ≤ ((18352677622761787 / 2305843009213693952 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2104 : ((603139000974303 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((263 / 8 : ℚ) : ℝ) ∧
    logKernel ((263 / 8 : ℚ) : ℝ) ≤ ((150784750243577 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2104
  constructor
  · exact (show ((603139000974303 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((146821420982094293 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((263 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((18352677622761787 / 2305843009213693952 : ℚ) : ℝ) ≤ ((150784750243577 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2105 : ((72272582916471471 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2105 / 64 : ℚ) : ℝ) ∧
    heightZ ((2105 / 64 : ℚ) : ℝ) ≤ ((144545165832942945 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((72272582916471471 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2105 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-587 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2105 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-587 / 192 : ℚ) : ℝ) ≤ ((144545165832942945 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2105 : ((292291182376577 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2105 / 64 : ℚ) : ℝ) ∧
    logKernel ((2105 / 64 : ℚ) : ℝ) ≤ ((584582364753159 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2105
  constructor
  · exact (show ((292291182376577 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((72272582916471471 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2105 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((144545165832942945 / 18446744073709551616 : ℚ) : ℝ) ≤ ((584582364753159 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2106 : ((142304200748888223 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1053 / 32 : ℚ) : ℝ) ∧
    heightZ ((1053 / 32 : ℚ) : ℝ) ≤ ((71152100374444113 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((142304200748888223 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1053 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-295 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1053 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-295 / 96 : ℚ) : ℝ) ≤ ((71152100374444113 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2106 : ((566596656207529 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1053 / 32 : ℚ) : ℝ) ∧
    logKernel ((1053 / 32 : ℚ) : ℝ) ≤ ((283298328103767 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2106
  constructor
  · exact (show ((566596656207529 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((142304200748888223 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1053 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((71152100374444113 / 9223372036854775808 : ℚ) : ℝ) ≤ ((283298328103767 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2107 : ((70048989304091413 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2107 / 64 : ℚ) : ℝ) ∧
    heightZ ((2107 / 64 : ℚ) : ℝ) ≤ ((140097978608182829 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((70048989304091413 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2107 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-593 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2107 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-593 / 192 : ℚ) : ℝ) ≤ ((140097978608182829 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2107 : ((549164309739505 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2107 / 64 : ℚ) : ℝ) ∧
    logKernel ((2107 / 64 : ℚ) : ℝ) ≤ ((274582154869755 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2107
  constructor
  · exact (show ((549164309739505 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((70048989304091413 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2107 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((140097978608182829 / 18446744073709551616 : ℚ) : ℝ) ≤ ((274582154869755 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2108 : ((68962980385707959 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((527 / 16 : ℚ) : ℝ) ∧
    heightZ ((527 / 16 : ℚ) : ℝ) ≤ ((137925960771415921 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((68962980385707959 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((527 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-149 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((527 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-149 / 48 : ℚ) : ℝ) ≤ ((137925960771415921 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2108 : ((532268300187789 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((527 / 16 : ℚ) : ℝ) ∧
    logKernel ((527 / 16 : ℚ) : ℝ) ≤ ((266134150093897 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2108
  constructor
  · exact (show ((532268300187789 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((68962980385707959 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((527 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((137925960771415921 / 18446744073709551616 : ℚ) : ℝ) ≤ ((266134150093897 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2109 : ((67893808475003351 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2109 / 64 : ℚ) : ℝ) ∧
    heightZ ((2109 / 64 : ℚ) : ℝ) ≤ ((135787616950006705 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((67893808475003351 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2109 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-599 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2109 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-599 / 192 : ℚ) : ℝ) ≤ ((135787616950006705 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2109 : ((128973031550059 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((2109 / 64 : ℚ) : ℝ) ∧
    logKernel ((2109 / 64 : ℚ) : ℝ) ≤ ((515892126200241 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2109
  constructor
  · exact (show ((128973031550059 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((67893808475003351 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2109 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((135787616950006705 / 18446744073709551616 : ℚ) : ℝ) ≤ ((515892126200241 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2110 : ((4177575783648025 / 576460752303423488 : ℚ) : ℝ) ≤ heightZ ((1055 / 32 : ℚ) : ℝ) ∧
    heightZ ((1055 / 32 : ℚ) : ℝ) ≤ ((133682425076736803 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((4177575783648025 / 576460752303423488 : ℚ) : ℝ) ≤ Real.exp (-((1055 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-301 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1055 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-301 / 96 : ℚ) : ℝ) ≤ ((133682425076736803 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2110 : ((500019794117933 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1055 / 32 : ℚ) : ℝ) ∧
    logKernel ((1055 / 32 : ℚ) : ℝ) ≤ ((250009897058969 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2110
  constructor
  · exact (show ((500019794117933 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((4177575783648025 / 576460752303423488 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1055 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((133682425076736803 / 18446744073709551616 : ℚ) : ℝ) ≤ ((250009897058969 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2111 : ((8225616948643115 / 1152921504606846976 : ℚ) : ℝ) ≤ heightZ ((2111 / 64 : ℚ) : ℝ) ∧
    heightZ ((2111 / 64 : ℚ) : ℝ) ≤ ((131609871178289843 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((8225616948643115 / 1152921504606846976 : ℚ) : ℝ) ≤ Real.exp (-((2111 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-605 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2111 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-605 / 192 : ℚ) : ℝ) ≤ ((131609871178289843 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2111 : ((30289737647195 / 4503599627370496 : ℚ) : ℝ) ≤ logKernel ((2111 / 64 : ℚ) : ℝ) ∧
    logKernel ((2111 / 64 : ℚ) : ℝ) ≤ ((484635802355125 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2111
  constructor
  · exact (show ((30289737647195 / 4503599627370496 : ℚ) : ℝ) ≤ zKernel ((8225616948643115 / 1152921504606846976 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2111 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((131609871178289843 / 18446744073709551616 : ℚ) : ℝ) ≤ ((484635802355125 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2112 : ((129569449249767139 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((33 / 1 : ℚ) : ℝ) ∧
    heightZ ((33 / 1 : ℚ) : ℝ) ≤ ((64784724624883571 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((129569449249767139 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((33 / 1 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-19 / 6 : ℚ) : ℝ) ∧
      Real.exp (-((33 / 1 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-19 / 6 : ℚ) : ℝ) ≤ ((64784724624883571 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2112 : ((469725126259691 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((33 / 1 : ℚ) : ℝ) ∧
    logKernel ((33 / 1 : ℚ) : ℝ) ≤ ((29357820391231 / 4503599627370496 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2112
  constructor
  · exact (show ((469725126259691 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((129569449249767139 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((33 / 1 : ℚ) : ℝ)) hh).trans
      (show zKernel ((64784724624883571 / 9223372036854775808 : ℚ) : ℝ) ≤ ((29357820391231 / 4503599627370496 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2113 : ((127560661131148835 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2113 / 64 : ℚ) : ℝ) ∧
    heightZ ((2113 / 64 : ℚ) : ℝ) ≤ ((63780330565574419 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((127560661131148835 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2113 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-611 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2113 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-611 / 192 : ℚ) : ℝ) ≤ ((63780330565574419 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2113 : ((455273203439489 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2113 / 64 : ℚ) : ℝ) ∧
    logKernel ((2113 / 64 : ℚ) : ℝ) ≤ ((227636601719747 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2113
  constructor
  · exact (show ((455273203439489 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((127560661131148835 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2113 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((63780330565574419 / 9223372036854775808 : ℚ) : ℝ) ≤ ((227636601719747 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2114 : ((62791508192835159 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((1057 / 32 : ℚ) : ℝ) ∧
    heightZ ((1057 / 32 : ℚ) : ℝ) ≤ ((125583016385670321 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((62791508192835159 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((1057 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-307 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1057 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-307 / 96 : ℚ) : ℝ) ≤ ((125583016385670321 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2114 : ((441265919540063 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1057 / 32 : ℚ) : ℝ) ∧
    logKernel ((1057 / 32 : ℚ) : ℝ) ≤ ((110316479885017 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2114
  constructor
  · exact (show ((441265919540063 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((62791508192835159 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1057 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((125583016385670321 / 18446744073709551616 : ℚ) : ℝ) ≤ ((110316479885017 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2115 : ((61818016090042125 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2115 / 64 : ℚ) : ℝ) ∧
    heightZ ((2115 / 64 : ℚ) : ℝ) ≤ ((123636032180084253 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((61818016090042125 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2115 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-617 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2115 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-617 / 192 : ℚ) : ℝ) ≤ ((123636032180084253 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2115 : ((427689594459993 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2115 / 64 : ℚ) : ℝ) ∧
    logKernel ((2115 / 64 : ℚ) : ℝ) ≤ ((213844797229999 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2115
  constructor
  · exact (show ((427689594459993 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((61818016090042125 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2115 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((123636032180084253 / 18446744073709551616 : ℚ) : ℝ) ≤ ((213844797229999 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2116 : ((7607452072923685 / 1152921504606846976 : ℚ) : ℝ) ≤ heightZ ((529 / 16 : ℚ) : ℝ) ∧
    heightZ ((529 / 16 : ℚ) : ℝ) ≤ ((121719233166778963 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((7607452072923685 / 1152921504606846976 : ℚ) : ℝ) ≤ Real.exp (-((529 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-155 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((529 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-155 / 48 : ℚ) : ℝ) ≤ ((121719233166778963 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2116 : ((414530968990335 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((529 / 16 : ℚ) : ℝ) ∧
    logKernel ((529 / 16 : ℚ) : ℝ) ≤ ((103632742247585 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2116
  constructor
  · exact (show ((414530968990335 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((7607452072923685 / 1152921504606846976 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((529 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((121719233166778963 / 18446744073709551616 : ℚ) : ℝ) ≤ ((103632742247585 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2117 : ((29958037841931105 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((2117 / 64 : ℚ) : ℝ) ∧
    heightZ ((2117 / 64 : ℚ) : ℝ) ≤ ((119832151367724423 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((29958037841931105 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((2117 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-623 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2117 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-623 / 192 : ℚ) : ℝ) ≤ ((119832151367724423 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2117 : ((100444297966279 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((2117 / 64 : ℚ) : ℝ) ∧
    logKernel ((2117 / 64 : ℚ) : ℝ) ≤ ((401777191865121 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2117
  constructor
  · exact (show ((100444297966279 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((29958037841931105 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2117 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((119832151367724423 / 18446744073709551616 : ℚ) : ℝ) ≤ ((401777191865121 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2118 : ((117974326060217469 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1059 / 32 : ℚ) : ℝ) ∧
    heightZ ((1059 / 32 : ℚ) : ℝ) ≤ ((921674422345449 / 144115188075855872 : ℚ) : ℝ) := by
  have h : ((117974326060217469 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1059 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-313 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1059 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-313 / 96 : ℚ) : ℝ) ≤ ((921674422345449 / 144115188075855872 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2118 : ((389415807210249 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1059 / 32 : ℚ) : ℝ) ∧
    logKernel ((1059 / 32 : ℚ) : ℝ) ≤ ((194707903605127 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2118
  constructor
  · exact (show ((389415807210249 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((117974326060217469 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1059 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((921674422345449 / 144115188075855872 : ℚ) : ℝ) ≤ ((194707903605127 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2119 : ((116145303664398399 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2119 / 64 : ℚ) : ℝ) ∧
    heightZ ((2119 / 64 : ℚ) : ℝ) ≤ ((58072651832199201 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((116145303664398399 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2119 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-629 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2119 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-629 / 192 : ℚ) : ℝ) ≤ ((58072651832199201 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2119 : ((188717371189303 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2119 / 64 : ℚ) : ℝ) ∧
    logKernel ((2119 / 64 : ℚ) : ℝ) ≤ ((377434742378611 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2119
  constructor
  · exact (show ((188717371189303 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((116145303664398399 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2119 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((58072651832199201 / 9223372036854775808 : ℚ) : ℝ) ≤ ((377434742378611 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2120 : ((28586159408127857 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((265 / 8 : ℚ) : ℝ) ∧
    heightZ ((265 / 8 : ℚ) : ℝ) ≤ ((114344637632511431 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((28586159408127857 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((265 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-79 / 24 : ℚ) : ℝ) ∧
      Real.exp (-((265 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-79 / 24 : ℚ) : ℝ) ≤ ((114344637632511431 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2120 : ((365822296159361 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((265 / 8 : ℚ) : ℝ) ∧
    logKernel ((265 / 8 : ℚ) : ℝ) ≤ ((182911148079683 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2120
  constructor
  · exact (show ((365822296159361 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((28586159408127857 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((265 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((114344637632511431 / 18446744073709551616 : ℚ) : ℝ) ≤ ((182911148079683 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2121 : ((112571888339882039 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2121 / 64 : ℚ) : ℝ) ∧
    heightZ ((2121 / 64 : ℚ) : ℝ) ≤ ((56285944169941021 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((112571888339882039 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2121 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-635 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2121 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-635 / 192 : ℚ) : ℝ) ≤ ((56285944169941021 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2121 : ((354567127350101 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2121 / 64 : ℚ) : ℝ) ∧
    logKernel ((2121 / 64 : ℚ) : ℝ) ≤ ((177283563675053 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2121
  constructor
  · exact (show ((354567127350101 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((112571888339882039 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2121 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((56285944169941021 / 9223372036854775808 : ℚ) : ℝ) ≤ ((177283563675053 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2122 : ((55413311488792273 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((1061 / 32 : ℚ) : ℝ) ∧
    heightZ ((1061 / 32 : ℚ) : ℝ) ≤ ((110826622977584549 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((55413311488792273 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((1061 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-319 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1061 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-319 / 96 : ℚ) : ℝ) ≤ ((110826622977584549 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2122 : ((85914560920131 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((1061 / 32 : ℚ) : ℝ) ∧
    logKernel ((1061 / 32 : ℚ) : ℝ) ≤ ((343658243680529 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2122
  constructor
  · exact (show ((85914560920131 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((55413311488792273 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1061 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((110826622977584549 / 18446744073709551616 : ℚ) : ℝ) ≤ ((343658243680529 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2123 : ((6819275965423357 / 1152921504606846976 : ℚ) : ℝ) ≤ heightZ ((2123 / 64 : ℚ) : ℝ) ∧
    heightZ ((2123 / 64 : ℚ) : ℝ) ≤ ((109108415446773715 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((6819275965423357 / 1152921504606846976 : ℚ) : ℝ) ≤ Real.exp (-((2123 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-641 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2123 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-641 / 192 : ℚ) : ℝ) ≤ ((109108415446773715 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2123 : ((166542495538467 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2123 / 64 : ℚ) : ℝ) ∧
    logKernel ((2123 / 64 : ℚ) : ℝ) ≤ ((333084991076939 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2123
  constructor
  · exact (show ((166542495538467 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((6819275965423357 / 1152921504606846976 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2123 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((109108415446773715 / 18446744073709551616 : ℚ) : ℝ) ≤ ((333084991076939 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2124 : ((107416846254654585 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((531 / 16 : ℚ) : ℝ) ∧
    heightZ ((531 / 16 : ℚ) : ℝ) ≤ ((26854211563663647 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((107416846254654585 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((531 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-161 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((531 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-161 / 48 : ℚ) : ℝ) ≤ ((26854211563663647 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2124 : ((322837043257021 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((531 / 16 : ℚ) : ℝ) ∧
    logKernel ((531 / 16 : ℚ) : ℝ) ≤ ((161418521628513 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2124
  constructor
  · exact (show ((322837043257021 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((107416846254654585 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((531 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((26854211563663647 / 4611686018427387904 : ℚ) : ℝ) ≤ ((161418521628513 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2125 : ((26437875603016297 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((2125 / 64 : ℚ) : ℝ) ∧
    heightZ ((2125 / 64 : ℚ) : ℝ) ≤ ((105751502412065191 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((26437875603016297 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((2125 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-647 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2125 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-647 / 192 : ℚ) : ℝ) ≤ ((105751502412065191 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2125 : ((156452195822391 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2125 / 64 : ℚ) : ℝ) ∧
    logKernel ((2125 / 64 : ℚ) : ℝ) ≤ ((312904391644787 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2125
  constructor
  · exact (show ((156452195822391 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((26437875603016297 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2125 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((105751502412065191 / 18446744073709551616 : ℚ) : ℝ) ≤ ((312904391644787 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2126 : ((52055988666323515 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((1063 / 32 : ℚ) : ℝ) ∧
    heightZ ((1063 / 32 : ℚ) : ℝ) ≤ ((104111977332647033 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((52055988666323515 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((1063 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-325 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1063 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-325 / 96 : ℚ) : ℝ) ≤ ((104111977332647033 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2126 : ((75819333898931 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((1063 / 32 : ℚ) : ℝ) ∧
    logKernel ((1063 / 32 : ℚ) : ℝ) ≤ ((303277335595729 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2126
  constructor
  · exact (show ((75819333898931 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((52055988666323515 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1063 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((104111977332647033 / 18446744073709551616 : ℚ) : ℝ) ≤ ((303277335595729 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2127 : ((102497870733578845 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2127 / 64 : ℚ) : ℝ) ∧
    heightZ ((2127 / 64 : ℚ) : ℝ) ≤ ((3203058460424339 / 576460752303423488 : ℚ) : ℝ) := by
  have h : ((102497870733578845 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2127 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-653 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2127 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-653 / 192 : ℚ) : ℝ) ≤ ((3203058460424339 / 576460752303423488 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2127 : ((293946472922811 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2127 / 64 : ℚ) : ℝ) ∧
    logKernel ((2127 / 64 : ℚ) : ℝ) ≤ ((4592913639419 / 1125899906842624 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2127
  constructor
  · exact (show ((293946472922811 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((102497870733578845 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2127 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((3203058460424339 / 576460752303423488 : ℚ) : ℝ) ≤ ((4592913639419 / 1125899906842624 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2128 : ((100908788537849299 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((133 / 4 : ℚ) : ℝ) ∧
    heightZ ((133 / 4 : ℚ) : ℝ) ≤ ((50454394268924651 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((100908788537849299 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((133 / 4 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-41 / 12 : ℚ) : ℝ) ∧
      Real.exp (-((133 / 4 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-41 / 12 : ℚ) : ℝ) ≤ ((50454394268924651 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2128 : ((142451345356945 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((133 / 4 : ℚ) : ℝ) ∧
    logKernel ((133 / 4 : ℚ) : ℝ) ≤ ((284902690713895 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2128
  constructor
  · exact (show ((142451345356945 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((100908788537849299 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((133 / 4 : ℚ) : ℝ)) hh).trans
      (show zKernel ((50454394268924651 / 9223372036854775808 : ℚ) : ℝ) ≤ ((284902690713895 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2129 : ((49672171389022415 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2129 / 64 : ℚ) : ℝ) ∧
    heightZ ((2129 / 64 : ℚ) : ℝ) ≤ ((99344342778044833 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((49672171389022415 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2129 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-659 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2129 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-659 / 192 : ℚ) : ℝ) ≤ ((99344342778044833 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2129 : ((276137156431637 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2129 / 64 : ℚ) : ℝ) ∧
    logKernel ((2129 / 64 : ℚ) : ℝ) ≤ ((138068578215821 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2129
  constructor
  · exact (show ((276137156431637 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((49672171389022415 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2129 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((99344342778044833 / 18446744073709551616 : ℚ) : ℝ) ≤ ((138068578215821 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem log_height_bounds_256 : ((125735338871209137 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((1049 / 32 : ℚ) : ℝ) ∧
    Real.log ((1049 / 32 : ℚ) : ℝ) ≤ ((251470677742418277 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((125735338871209137 / 36028797018963968 : ℚ) : ℝ) ≤ ((1049 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1049 / 32 : ℚ) : ℝ) ≤ Real.exp ((251470677742418277 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_256 : heightPower (256 : Fin 988) ≤ ((1162627241886587 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_256
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_256 : heightFactor (256 : Fin 988) ≤ ((768228992026101 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_256
  obtain ⟨hpl, hph⟩ := kernel_bounds_2097
  obtain ⟨hcl, hch⟩ := kernel_bounds_2098
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2098
  have h : (((1100401 / 512 : ℚ) : ℝ) * (logKernel ((2097 / 64 : ℚ) : ℝ) - logKernel ((1049 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1049 / 32 : ℚ) : ℝ) + Real.log ((1049 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((768228992026101 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_257 : ((62876253852497767 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((2099 / 64 : ℚ) : ℝ) ∧
    Real.log ((2099 / 64 : ℚ) : ℝ) ≤ ((251505015409991071 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((62876253852497767 / 18014398509481984 : ℚ) : ℝ) ≤ ((2099 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2099 / 64 : ℚ) : ℝ) ≤ Real.exp ((251505015409991071 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_257 : heightPower (257 : Fin 988) ≤ ((1167159419911647 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_257
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_257 : heightFactor (257 : Fin 988) ≤ ((374656989805701 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_257
  obtain ⟨hpl, hph⟩ := kernel_bounds_2098
  obtain ⟨hcl, hch⟩ := kernel_bounds_2099
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2099
  have h : (((4405801 / 2048 : ℚ) : ℝ) * (logKernel ((1049 / 32 : ℚ) : ℝ) - logKernel ((2099 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2099 / 64 : ℚ) : ℝ) + Real.log ((2099 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((374656989805701 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_258 : ((62884834180599721 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((525 / 16 : ℚ) : ℝ) ∧
    Real.log ((525 / 16 : ℚ) : ℝ) ≤ ((251539336722398887 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((62884834180599721 / 18014398509481984 : ℚ) : ℝ) ≤ ((525 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((525 / 16 : ℚ) : ℝ) ≤ Real.exp ((251539336722398887 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_258 : heightPower (258 : Fin 988) ≤ ((18307680219521 / 4398046511104 : ℚ) : ℝ) := by
  have hh := log_height_bounds_258
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_258 : heightFactor (258 : Fin 988) ≤ ((730864297639147 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_258
  obtain ⟨hpl, hph⟩ := kernel_bounds_2099
  obtain ⟨hcl, hch⟩ := kernel_bounds_2100
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2100
  have h : (((275625 / 128 : ℚ) : ℝ) * (logKernel ((2099 / 64 : ℚ) : ℝ) - logKernel ((525 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((525 / 16 : ℚ) : ℝ) + Real.log ((525 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((730864297639147 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_259 : ((125786820847607181 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2101 / 64 : ℚ) : ℝ) ∧
    Real.log ((2101 / 64 : ℚ) : ℝ) ≤ ((251573641695214365 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((125786820847607181 / 36028797018963968 : ℚ) : ℝ) ≤ ((2101 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2101 / 64 : ℚ) : ℝ) ≤ Real.exp ((251573641695214365 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_259 : heightPower (259 : Fin 988) ≤ ((1176223584360509 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_259
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_259 : heightFactor (259 : Fin 988) ≤ ((712868508358711 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_259
  obtain ⟨hpl, hph⟩ := kernel_bounds_2100
  obtain ⟨hcl, hch⟩ := kernel_bounds_2101
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2101
  have h : (((4414201 / 2048 : ℚ) : ℝ) * (logKernel ((525 / 16 : ℚ) : ℝ) - logKernel ((2101 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2101 / 64 : ℚ) : ℝ) + Real.log ((2101 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((712868508358711 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_260 : ((251607930343987913 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1051 / 32 : ℚ) : ℝ) ∧
    Real.log ((1051 / 32 : ℚ) : ℝ) ≤ ((62901982585996979 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((251607930343987913 / 72057594037927936 : ℚ) : ℝ) ≤ ((1051 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1051 / 32 : ℚ) : ℝ) ≤ Real.exp ((62901982585996979 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_260 : heightPower (260 : Fin 988) ≤ ((295188892726471 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_260
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_260 : heightFactor (260 : Fin 988) ≤ ((10864303982883 / 4398046511104 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_260
  obtain ⟨hpl, hph⟩ := kernel_bounds_2101
  obtain ⟨hcl, hch⟩ := kernel_bounds_2102
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2102
  have h : (((1104601 / 512 : ℚ) : ℝ) * (logKernel ((2101 / 64 : ℚ) : ℝ) - logKernel ((1051 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1051 / 32 : ℚ) : ℝ) + Real.log ((1051 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((10864303982883 / 4398046511104 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_261 : ((125821101342123879 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2103 / 64 : ℚ) : ℝ) ∧
    Real.log ((2103 / 64 : ℚ) : ℝ) ≤ ((251642202684247761 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((125821101342123879 / 36028797018963968 : ℚ) : ℝ) ≤ ((2103 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2103 / 64 : ℚ) : ℝ) ≤ Real.exp ((251642202684247761 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_261 : heightPower (261 : Fin 988) ≤ ((74080468359133 / 17592186044416 : ℚ) : ℝ) := by
  have hh := log_height_bounds_261
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_261 : heightFactor (261 : Fin 988) ≤ ((678194254404583 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_261
  obtain ⟨hpl, hph⟩ := kernel_bounds_2102
  obtain ⟨hcl, hch⟩ := kernel_bounds_2103
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2103
  have h : (((4422609 / 2048 : ℚ) : ℝ) * (logKernel ((1051 / 32 : ℚ) : ℝ) - logKernel ((2103 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2103 / 64 : ℚ) : ℝ) + Real.log ((2103 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((678194254404583 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_262 : ((251676458731499973 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((263 / 8 : ℚ) : ℝ) ∧
    Real.log ((263 / 8 : ℚ) : ℝ) ≤ ((31459557341437497 / 9007199254740992 : ℚ) : ℝ) := by
  have hl : Real.exp ((251676458731499973 / 72057594037927936 : ℚ) : ℝ) ≤ ((263 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((263 / 8 : ℚ) : ℝ) ≤ Real.exp ((31459557341437497 / 9007199254740992 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_262 : heightPower (262 : Fin 988) ≤ ((1189819352941811 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_262
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_262 : heightFactor (262 : Fin 988) ≤ ((330747145629031 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_262
  obtain ⟨hpl, hph⟩ := kernel_bounds_2103
  obtain ⟨hcl, hch⟩ := kernel_bounds_2104
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2104
  have h : (((69169 / 32 : ℚ) : ℝ) * (logKernel ((2103 / 64 : ℚ) : ℝ) - logKernel ((263 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((263 / 8 : ℚ) : ℝ) + Real.log ((263 / 8 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((330747145629031 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_263 : ((15731918656326783 / 4503599627370496 : ℚ) : ℝ) ≤ Real.log ((2105 / 64 : ℚ) : ℝ) ∧
    Real.log ((2105 / 64 : ℚ) : ℝ) ≤ ((251710698501228531 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((15731918656326783 / 4503599627370496 : ℚ) : ℝ) ≤ ((2105 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2105 / 64 : ℚ) : ℝ) ≤ Real.exp ((251710698501228531 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_263 : heightPower (263 : Fin 988) ≤ ((1194351148553417 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_263
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_263 : heightFactor (263 : Fin 988) ≤ ((80650651322183 / 35184372088832 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_263
  obtain ⟨hpl, hph⟩ := kernel_bounds_2104
  obtain ⟨hcl, hch⟩ := kernel_bounds_2105
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2105
  have h : (((4431025 / 2048 : ℚ) : ℝ) * (logKernel ((263 / 8 : ℚ) : ℝ) - logKernel ((2105 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2105 / 64 : ℚ) : ℝ) + Real.log ((2105 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((80650651322183 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_264 : ((62936230502223833 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((1053 / 32 : ℚ) : ℝ) ∧
    Real.log ((1053 / 32 : ℚ) : ℝ) ≤ ((251744922008895335 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((62936230502223833 / 18014398509481984 : ℚ) : ℝ) ≤ ((1053 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1053 / 32 : ℚ) : ℝ) ≤ Real.exp ((251744922008895335 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_264 : heightPower (264 : Fin 988) ≤ ((1198882880641345 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_264
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_264 : heightFactor (264 : Fin 988) ≤ ((314658455895843 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_264
  obtain ⟨hpl, hph⟩ := kernel_bounds_2105
  obtain ⟨hcl, hch⟩ := kernel_bounds_2106
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2106
  have h : (((1108809 / 512 : ℚ) : ℝ) * (logKernel ((2105 / 64 : ℚ) : ℝ) - logKernel ((1053 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1053 / 32 : ℚ) : ℝ) + Real.log ((1053 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((314658455895843 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_265 : ((125889564634970137 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2107 / 64 : ℚ) : ℝ) ∧
    Real.log ((2107 / 64 : ℚ) : ℝ) ≤ ((251779129269940277 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((125889564634970137 / 36028797018963968 : ℚ) : ℝ) ≤ ((2107 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2107 / 64 : ℚ) : ℝ) ≤ Real.exp ((251779129269940277 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_265 : heightPower (265 : Fin 988) ≤ ((601707274632953 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_265
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_265 : heightFactor (265 : Fin 988) ≤ ((613819542405827 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_265
  obtain ⟨hpl, hph⟩ := kernel_bounds_2106
  obtain ⟨hcl, hch⟩ := kernel_bounds_2107
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2107
  have h : (((4439449 / 2048 : ℚ) : ℝ) * (logKernel ((1053 / 32 : ℚ) : ℝ) - logKernel ((2107 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2107 / 64 : ℚ) : ℝ) + Real.log ((2107 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((613819542405827 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_266 : ((15738332518736329 / 4503599627370496 : ℚ) : ℝ) ≤ Real.log ((527 / 16 : ℚ) : ℝ) ∧
    Real.log ((527 / 16 : ℚ) : ℝ) ≤ ((251813320299781267 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((15738332518736329 / 4503599627370496 : ℚ) : ℝ) ≤ ((527 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((527 / 16 : ℚ) : ℝ) ≤ Real.exp ((251813320299781267 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_266 : heightPower (266 : Fin 988) ≤ ((603973077243663 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_266
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_266 : heightFactor (266 : Fin 988) ≤ ((37418968244623 / 17592186044416 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_266
  obtain ⟨hpl, hph⟩ := kernel_bounds_2107
  obtain ⟨hcl, hch⟩ := kernel_bounds_2108
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2108
  have h : (((277729 / 128 : ℚ) : ℝ) * (logKernel ((2107 / 64 : ℚ) : ℝ) - logKernel ((527 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((527 / 16 : ℚ) : ℝ) + Real.log ((527 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((37418968244623 / 17592186044416 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_267 : ((251847495113814275 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2109 / 64 : ℚ) : ℝ) ∧
    Real.log ((2109 / 64 : ℚ) : ℝ) ≤ ((125923747556907139 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((251847495113814275 / 72057594037927936 : ℚ) : ℝ) ≤ ((2109 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2109 / 64 : ℚ) : ℝ) ≤ Real.exp ((125923747556907139 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_267 : heightPower (267 : Fin 988) ≤ ((1212477696365747 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_267
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_267 : heightFactor (267 : Fin 988) ≤ ((291979692930591 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_267
  obtain ⟨hpl, hph⟩ := kernel_bounds_2108
  obtain ⟨hcl, hch⟩ := kernel_bounds_2109
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2109
  have h : (((4447881 / 2048 : ℚ) : ℝ) * (logKernel ((527 / 16 : ℚ) : ℝ) - logKernel ((2109 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2109 / 64 : ℚ) : ℝ) + Real.log ((2109 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((291979692930591 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_268 : ((125940826863706693 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((1055 / 32 : ℚ) : ℝ) ∧
    Real.log ((1055 / 32 : ℚ) : ℝ) ≤ ((251881653727413389 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((125940826863706693 / 36028797018963968 : ℚ) : ℝ) ≤ ((1055 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1055 / 32 : ℚ) : ℝ) ≤ Real.exp ((251881653727413389 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_268 : heightPower (268 : Fin 988) ≤ ((608504587480611 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_268
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_268 : heightFactor (268 : Fin 988) ≤ ((569578080051099 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_268
  obtain ⟨hpl, hph⟩ := kernel_bounds_2109
  obtain ⟨hcl, hch⟩ := kernel_bounds_2110
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2110
  have h : (((1113025 / 512 : ℚ) : ℝ) * (logKernel ((2109 / 64 : ℚ) : ℝ) - logKernel ((1055 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1055 / 32 : ℚ) : ℝ) + Real.log ((1055 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((569578080051099 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_269 : ((62978949038982705 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((2111 / 64 : ℚ) : ℝ) ∧
    Real.log ((2111 / 64 : ℚ) : ℝ) ≤ ((251915796155930823 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((62978949038982705 / 18014398509481984 : ℚ) : ℝ) ≤ ((2111 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2111 / 64 : ℚ) : ℝ) ≤ Real.exp ((251915796155930823 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_269 : heightPower (269 : Fin 988) ≤ ((610770295166861 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_269
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_269 : heightFactor (269 : Fin 988) ≤ ((69443831861935 / 35184372088832 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_269
  obtain ⟨hpl, hph⟩ := kernel_bounds_2110
  obtain ⟨hcl, hch⟩ := kernel_bounds_2111
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2111
  have h : (((4456321 / 2048 : ℚ) : ℝ) * (logKernel ((1055 / 32 : ℚ) : ℝ) - logKernel ((2111 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2111 / 64 : ℚ) : ℝ) + Real.log ((2111 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((69443831861935 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_270 : ((251949922414696991 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((33 / 1 : ℚ) : ℝ) ∧
    Real.log ((33 / 1 : ℚ) : ℝ) ≤ ((125974961207348497 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((251949922414696991 / 72057594037927936 : ℚ) : ℝ) ≤ ((33 / 1 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((33 / 1 : ℚ) : ℝ) ≤ Real.exp ((125974961207348497 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_270 : heightPower (270 : Fin 988) ≤ ((306517985635783 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_270
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_270 : heightFactor (270 : Fin 988) ≤ ((135467102475579 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_270
  obtain ⟨hpl, hph⟩ := kernel_bounds_2111
  obtain ⟨hcl, hch⟩ := kernel_bounds_2112
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2112
  have h : (((2178 / 1 : ℚ) : ℝ) * (logKernel ((2111 / 64 : ℚ) : ℝ) - logKernel ((33 / 1 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((33 / 1 : ℚ) : ℝ) + Real.log ((33 / 1 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((135467102475579 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_271 : ((125992016259510269 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2113 / 64 : ℚ) : ℝ) ∧
    Real.log ((2113 / 64 : ℚ) : ℝ) ≤ ((251984032519020541 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((125992016259510269 / 36028797018963968 : ℚ) : ℝ) ≤ ((2113 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2113 / 64 : ℚ) : ℝ) ≤ Real.exp ((251984032519020541 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_271 : heightPower (271 : Fin 988) ≤ ((1230603231649249 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_271
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_271 : heightFactor (271 : Fin 988) ≤ ((264261429149527 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_271
  obtain ⟨hpl, hph⟩ := kernel_bounds_2112
  obtain ⟨hcl, hch⟩ := kernel_bounds_2113
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2113
  have h : (((4464769 / 2048 : ℚ) : ℝ) * (logKernel ((33 / 1 : ℚ) : ℝ) - logKernel ((2113 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2113 / 64 : ℚ) : ℝ) + Real.log ((2113 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((264261429149527 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_272 : ((126009063242094187 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((1057 / 32 : ℚ) : ℝ) ∧
    Real.log ((1057 / 32 : ℚ) : ℝ) ≤ ((252018126484188377 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((126009063242094187 / 36028797018963968 : ℚ) : ℝ) ≤ ((1057 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1057 / 32 : ℚ) : ℝ) ≤ Real.exp ((252018126484188377 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_272 : heightPower (272 : Fin 988) ≤ ((617567228855895 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_272
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_272 : heightFactor (272 : Fin 988) ≤ ((257752860893823 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_272
  obtain ⟨hpl, hph⟩ := kernel_bounds_2113
  obtain ⟨hcl, hch⟩ := kernel_bounds_2114
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2114
  have h : (((1117249 / 512 : ℚ) : ℝ) * (logKernel ((2113 / 64 : ℚ) : ℝ) - logKernel ((1057 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1057 / 32 : ℚ) : ℝ) + Real.log ((1057 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((257752860893823 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_273 : ((252052204325465721 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2115 / 64 : ℚ) : ℝ) ∧
    Real.log ((2115 / 64 : ℚ) : ℝ) ≤ ((63013051081366431 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((252052204325465721 / 72057594037927936 : ℚ) : ℝ) ≤ ((2115 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2115 / 64 : ℚ) : ℝ) ≤ Real.exp ((63013051081366431 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_273 : heightPower (273 : Fin 988) ≤ ((77479101299399 / 17592186044416 : ℚ) : ℝ) := by
  have hh := log_height_bounds_273
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_273 : heightFactor (273 : Fin 988) ≤ ((502808925428195 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_273
  obtain ⟨hpl, hph⟩ := kernel_bounds_2114
  obtain ⟨hcl, hch⟩ := kernel_bounds_2115
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2115
  have h : (((4473225 / 2048 : ℚ) : ℝ) * (logKernel ((1057 / 32 : ℚ) : ℝ) - logKernel ((2115 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2115 / 64 : ℚ) : ℝ) + Real.log ((2115 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((502808925428195 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_274 : ((126043133029048077 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((529 / 16 : ℚ) : ℝ) ∧
    Real.log ((529 / 16 : ℚ) : ℝ) ≤ ((252086266058096157 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((126043133029048077 / 36028797018963968 : ℚ) : ℝ) ≤ ((529 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((529 / 16 : ℚ) : ℝ) ≤ Real.exp ((252086266058096157 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_274 : heightPower (274 : Fin 988) ≤ ((19440573764759 / 4398046511104 : ℚ) : ℝ) := by
  have hh := log_height_bounds_274
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_274 : heightFactor (274 : Fin 988) ≤ ((490424592648041 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_274
  obtain ⟨hpl, hph⟩ := kernel_bounds_2115
  obtain ⟨hcl, hch⟩ := kernel_bounds_2116
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2116
  have h : (((279841 / 128 : ℚ) : ℝ) * (logKernel ((2115 / 64 : ℚ) : ℝ) - logKernel ((529 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((529 / 16 : ℚ) : ℝ) + Real.log ((529 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((490424592648041 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_275 : ((252120311697301641 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2117 / 64 : ℚ) : ℝ) ∧
    Real.log ((2117 / 64 : ℚ) : ℝ) ≤ ((63030077924325411 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((252120311697301641 / 72057594037927936 : ℚ) : ℝ) ≤ ((2117 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2117 / 64 : ℚ) : ℝ) ≤ Real.exp ((63030077924325411 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_275 : heightPower (275 : Fin 988) ≤ ((624363879116913 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_275
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_275 : heightFactor (275 : Fin 988) ≤ ((478345040373217 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_275
  obtain ⟨hpl, hph⟩ := kernel_bounds_2116
  obtain ⟨hcl, hch⟩ := kernel_bounds_2117
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2117
  have h : (((4481689 / 2048 : ℚ) : ℝ) * (logKernel ((529 / 16 : ℚ) : ℝ) - logKernel ((2117 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2117 / 64 : ℚ) : ℝ) + Real.log ((2117 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((478345040373217 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_276 : ((31519292657285323 / 9007199254740992 : ℚ) : ℝ) ≤ Real.log ((1059 / 32 : ℚ) : ℝ) ∧
    Real.log ((1059 / 32 : ℚ) : ℝ) ≤ ((252154341258282587 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((31519292657285323 / 9007199254740992 : ℚ) : ℝ) ≤ ((1059 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1059 / 32 : ℚ) : ℝ) ≤ Real.exp ((252154341258282587 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_276 : heightPower (276 : Fin 988) ≤ ((156657341589689 / 35184372088832 : ℚ) : ℝ) := by
  have hh := log_height_bounds_276
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_276 : heightFactor (276 : Fin 988) ≤ ((116640693569821 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_276
  obtain ⟨hpl, hph⟩ := kernel_bounds_2117
  obtain ⟨hcl, hch⟩ := kernel_bounds_2118
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2118
  have h : (((1121481 / 512 : ℚ) : ℝ) * (logKernel ((2117 / 64 : ℚ) : ℝ) - logKernel ((1059 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1059 / 32 : ℚ) : ℝ) + Real.log ((1059 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((116640693569821 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_277 : ((252188354756217861 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2119 / 64 : ℚ) : ℝ) ∧
    Real.log ((2119 / 64 : ℚ) : ℝ) ≤ ((31523544344527233 / 9007199254740992 : ℚ) : ℝ) := by
  have hl : Real.exp ((252188354756217861 / 72057594037927936 : ℚ) : ℝ) ≤ ((2119 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2119 / 64 : ℚ) : ℝ) ≤ Real.exp ((31523544344527233 / 9007199254740992 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_277 : heightPower (277 : Fin 988) ≤ ((628894822227463 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_277
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_277 : heightFactor (277 : Fin 988) ≤ ((113767621039653 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_277
  obtain ⟨hpl, hph⟩ := kernel_bounds_2118
  obtain ⟨hcl, hch⟩ := kernel_bounds_2119
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2119
  have h : (((4490161 / 2048 : ℚ) : ℝ) * (logKernel ((1059 / 32 : ℚ) : ℝ) - logKernel ((2119 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2119 / 64 : ℚ) : ℝ) + Real.log ((2119 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((113767621039653 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_278 : ((252222352206264863 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((265 / 8 : ℚ) : ℝ) ∧
    Real.log ((265 / 8 : ℚ) : ℝ) ≤ ((126111176103132433 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((252222352206264863 / 72057594037927936 : ℚ) : ℝ) ≤ ((265 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((265 / 8 : ℚ) : ℝ) ≤ Real.exp ((126111176103132433 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_278 : heightPower (278 : Fin 988) ≤ ((315580123376319 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_278
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_278 : heightFactor (278 : Fin 988) ≤ ((443861039401257 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_278
  obtain ⟨hpl, hph⟩ := kernel_bounds_2119
  obtain ⟨hcl, hch⟩ := kernel_bounds_2120
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2120
  have h : (((70225 / 32 : ℚ) : ℝ) * (logKernel ((2119 / 64 : ℚ) : ℝ) - logKernel ((265 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((265 / 8 : ℚ) : ℝ) + Real.log ((265 / 8 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((443861039401257 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_279 : ((252256333623559539 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2121 / 64 : ℚ) : ℝ) ∧
    Real.log ((2121 / 64 : ℚ) : ℝ) ≤ ((126128166811779771 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((252256333623559539 / 72057594037927936 : ℚ) : ℝ) ≤ ((2121 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2121 / 64 : ℚ) : ℝ) ≤ Real.exp ((126128166811779771 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_279 : heightPower (279 : Fin 988) ≤ ((1266851279927687 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_279
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_279 : heightFactor (279 : Fin 988) ≤ ((432927484586657 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_279
  obtain ⟨hpl, hph⟩ := kernel_bounds_2120
  obtain ⟨hcl, hch⟩ := kernel_bounds_2121
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2121
  have h : (((4498641 / 2048 : ℚ) : ℝ) * (logKernel ((265 / 8 : ℚ) : ℝ) - logKernel ((2121 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2121 / 64 : ℚ) : ℝ) + Real.log ((2121 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((432927484586657 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_280 : ((252290299023216433 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1061 / 32 : ℚ) : ℝ) ∧
    Real.log ((1061 / 32 : ℚ) : ℝ) ≤ ((63072574755804109 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((252290299023216433 / 72057594037927936 : ℚ) : ℝ) ≤ ((1061 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1061 / 32 : ℚ) : ℝ) ≤ Real.exp ((63072574755804109 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_280 : heightPower (280 : Fin 988) ≤ ((1271382003781201 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_280
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_280 : heightFactor (280 : Fin 988) ≤ ((211131517591713 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_280
  obtain ⟨hpl, hph⟩ := kernel_bounds_2121
  obtain ⟨hcl, hch⟩ := kernel_bounds_2122
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2122
  have h : (((1125721 / 512 : ℚ) : ℝ) * (logKernel ((2121 / 64 : ℚ) : ℝ) - logKernel ((1061 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1061 / 32 : ℚ) : ℝ) + Real.log ((1061 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((211131517591713 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_281 : ((31540531052541091 / 9007199254740992 : ℚ) : ℝ) ≤ Real.log ((2123 / 64 : ℚ) : ℝ) ∧
    Real.log ((2123 / 64 : ℚ) : ℝ) ≤ ((252324248420328731 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((31540531052541091 / 9007199254740992 : ℚ) : ℝ) ≤ ((2123 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2123 / 64 : ℚ) : ℝ) ≤ Real.exp ((252324248420328731 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_281 : heightPower (281 : Fin 988) ≤ ((1275912665124775 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_281
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_281 : heightFactor (281 : Fin 988) ≤ ((102965268338649 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_281
  obtain ⟨hpl, hph⟩ := kernel_bounds_2122
  obtain ⟨hcl, hch⟩ := kernel_bounds_2123
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2123
  have h : (((4507129 / 2048 : ℚ) : ℝ) * (logKernel ((1061 / 32 : ℚ) : ℝ) - logKernel ((2123 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2123 / 64 : ℚ) : ℝ) + Real.log ((2123 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((102965268338649 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_282 : ((31544772728746035 / 9007199254740992 : ℚ) : ℝ) ≤ Real.log ((531 / 16 : ℚ) : ℝ) ∧
    Real.log ((531 / 16 : ℚ) : ℝ) ≤ ((252358181829968283 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((31544772728746035 / 9007199254740992 : ℚ) : ℝ) ≤ ((531 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((531 / 16 : ℚ) : ℝ) ≤ Real.exp ((252358181829968283 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_282 : heightPower (282 : Fin 988) ≤ ((1280443264017283 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_282
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_282 : heightFactor (282 : Fin 988) ≤ ((200857571932867 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_282
  obtain ⟨hpl, hph⟩ := kernel_bounds_2123
  obtain ⟨hcl, hch⟩ := kernel_bounds_2124
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2124
  have h : (((281961 / 128 : ℚ) : ℝ) * (logKernel ((2123 / 64 : ℚ) : ℝ) - logKernel ((531 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((531 / 16 : ℚ) : ℝ) + Real.log ((531 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((200857571932867 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_283 : ((126196049633592833 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2125 / 64 : ℚ) : ℝ) ∧
    Real.log ((2125 / 64 : ℚ) : ℝ) ≤ ((252392099267185669 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((126196049633592833 / 36028797018963968 : ℚ) : ℝ) ≤ ((2125 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2125 / 64 : ℚ) : ℝ) ≤ Real.exp ((252392099267185669 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_283 : heightPower (283 : Fin 988) ≤ ((642486900258759 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_283
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_283 : heightFactor (283 : Fin 988) ≤ ((391818950093403 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_283
  obtain ⟨hpl, hph⟩ := kernel_bounds_2124
  obtain ⟨hcl, hch⟩ := kernel_bounds_2125
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2125
  have h : (((4515625 / 2048 : ℚ) : ℝ) * (logKernel ((531 / 16 : ℚ) : ℝ) - logKernel ((2125 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2125 / 64 : ℚ) : ℝ) + Real.log ((2125 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((391818950093403 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_284 : ((126213000373505109 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((1063 / 32 : ℚ) : ℝ) ∧
    Real.log ((1063 / 32 : ℚ) : ℝ) ≤ ((252426000747010221 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((126213000373505109 / 36028797018963968 : ℚ) : ℝ) ≤ ((1063 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1063 / 32 : ℚ) : ℝ) ≤ Real.exp ((252426000747010221 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_284 : heightPower (284 : Fin 988) ≤ ((644752137342093 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_284
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_284 : heightFactor (284 : Fin 988) ≤ ((382166350131517 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_284
  obtain ⟨hpl, hph⟩ := kernel_bounds_2125
  obtain ⟨hcl, hch⟩ := kernel_bounds_2126
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2126
  have h : (((1129969 / 512 : ℚ) : ℝ) * (logKernel ((2125 / 64 : ℚ) : ℝ) - logKernel ((1063 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1063 / 32 : ℚ) : ℝ) + Real.log ((1063 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((382166350131517 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_285 : ((126229943142225033 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2127 / 64 : ℚ) : ℝ) ∧
    Real.log ((2127 / 64 : ℚ) : ℝ) ≤ ((252459886284450069 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((126229943142225033 / 36028797018963968 : ℚ) : ℝ) ≤ ((2127 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2127 / 64 : ℚ) : ℝ) ≤ Real.exp ((252459886284450069 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_285 : heightPower (285 : Fin 988) ≤ ((1294034686575915 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_285
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_285 : heightFactor (285 : Fin 988) ≤ ((186375676496589 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_285
  obtain ⟨hpl, hph⟩ := kernel_bounds_2126
  obtain ⟨hcl, hch⟩ := kernel_bounds_2127
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2127
  have h : (((4524129 / 2048 : ℚ) : ℝ) * (logKernel ((1063 / 32 : ℚ) : ℝ) - logKernel ((2127 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2127 / 64 : ℚ) : ℝ) + Real.log ((2127 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((186375676496589 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_286 : ((252493755894492175 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((133 / 4 : ℚ) : ℝ) ∧
    Real.log ((133 / 4 : ℚ) : ℝ) ≤ ((126246877947246089 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((252493755894492175 / 72057594037927936 : ℚ) : ℝ) ≤ ((133 / 4 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((133 / 4 : ℚ) : ℝ) ≤ Real.exp ((126246877947246089 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_286 : heightPower (286 : Fin 988) ≤ ((649282518125623 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_286
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_286 : heightFactor (286 : Fin 988) ≤ ((181784057452841 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_286
  obtain ⟨hpl, hph⟩ := kernel_bounds_2127
  obtain ⟨hcl, hch⟩ := kernel_bounds_2128
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2128
  have h : (((17689 / 8 : ℚ) : ℝ) * (logKernel ((2127 / 64 : ℚ) : ℝ) - logKernel ((133 / 4 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((133 / 4 : ℚ) : ℝ) + Real.log ((133 / 4 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((181784057452841 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_287 : ((252527609592102389 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2129 / 64 : ℚ) : ℝ) ∧
    Real.log ((2129 / 64 : ℚ) : ℝ) ≤ ((31565951199012799 / 9007199254740992 : ℚ) : ℝ) := by
  have hl : Real.exp ((252527609592102389 / 72057594037927936 : ℚ) : ℝ) ≤ ((2129 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2129 / 64 : ℚ) : ℝ) ≤ Real.exp ((31565951199012799 / 9007199254740992 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_287 : heightPower (287 : Fin 988) ≤ ((1303095323768639 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_287
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_287 : heightFactor (287 : Fin 988) ≤ ((354610935696373 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_287
  obtain ⟨hpl, hph⟩ := kernel_bounds_2128
  obtain ⟨hcl, hch⟩ := kernel_bounds_2129
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2129
  have h : (((4532641 / 2048 : ℚ) : ℝ) * (logKernel ((133 / 4 : ℚ) : ℝ) - logKernel ((2129 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2129 / 64 : ℚ) : ℝ) + Real.log ((2129 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((354610935696373 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

end LegendreK6.M2Pilot.Enclosures.Height008
