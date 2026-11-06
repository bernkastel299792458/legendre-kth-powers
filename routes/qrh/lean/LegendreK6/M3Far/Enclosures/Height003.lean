import LegendreK6.M3FarDefinitions
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp

/-! Generated proposals: every bound is checked by Lean, not by trusting Arb. -/
namespace LegendreK6.M3Far.Enclosures.Height003
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem height_z_bounds_891 : ((56351230601769 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((891 / 8 : ℚ) : ℝ) ∧
    heightZ ((891 / 8 : ℚ) : ℝ) ≤ ((14087807650443 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((56351230601769 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((891 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-181 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((891 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-181 / 16 : ℚ) : ℝ) ≤ ((14087807650443 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_891 : ((88847531 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((891 / 8 : ℚ) : ℝ) ∧
    logKernel ((891 / 8 : ℚ) : ℝ) ≤ ((5552971 / 4503599627370496 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_891
  constructor
  · exact (show ((88847531 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((56351230601769 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((891 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((14087807650443 / 4611686018427387904 : ℚ) : ℝ) ≤ ((5552971 / 4503599627370496 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_892 : ((49729786462891 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((223 / 2 : ℚ) : ℝ) ∧
    heightZ ((223 / 2 : ℚ) : ℝ) ≤ ((24864893231447 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((49729786462891 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((223 / 2 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-183 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((223 / 2 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-183 / 16 : ℚ) : ℝ) ≤ ((24864893231447 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_892 : ((34597263 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((223 / 2 : ℚ) : ℝ) ∧
    logKernel ((223 / 2 : ℚ) : ℝ) ≤ ((69194531 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_892
  constructor
  · exact (show ((34597263 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((49729786462891 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((223 / 2 : ℚ) : ℝ)) hh).trans
      (show zKernel ((24864893231447 / 9223372036854775808 : ℚ) : ℝ) ≤ ((69194531 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_893 : ((43886382519695 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((893 / 8 : ℚ) : ℝ) ∧
    heightZ ((893 / 8 : ℚ) : ℝ) ≤ ((21943191259849 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((43886382519695 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((893 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-185 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((893 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-185 / 16 : ℚ) : ℝ) ≤ ((21943191259849 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_893 : ((53888751 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((893 / 8 : ℚ) : ℝ) ∧
    logKernel ((893 / 8 : ℚ) : ℝ) ≤ ((13472189 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_893
  constructor
  · exact (show ((53888751 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((43886382519695 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((893 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((21943191259849 / 9223372036854775808 : ℚ) : ℝ) ≤ ((13472189 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_894 : ((38729596639273 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((447 / 4 : ℚ) : ℝ) ∧
    heightZ ((447 / 4 : ℚ) : ℝ) ≤ ((9682399159819 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((38729596639273 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((447 / 4 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-187 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((447 / 4 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-187 / 16 : ℚ) : ℝ) ≤ ((9682399159819 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_894 : ((41968601 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((447 / 4 : ℚ) : ℝ) ∧
    logKernel ((447 / 4 : ℚ) : ℝ) ≤ ((20984303 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_894
  constructor
  · exact (show ((41968601 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((38729596639273 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((447 / 4 : ℚ) : ℝ)) hh).trans
      (show zKernel ((9682399159819 / 4611686018427387904 : ℚ) : ℝ) ≤ ((20984303 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_895 : ((34178749072509 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((895 / 8 : ℚ) : ℝ) ∧
    heightZ ((895 / 8 : ℚ) : ℝ) ≤ ((267021477129 / 144115188075855872 : ℚ) : ℝ) := by
  have h : ((34178749072509 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((895 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-189 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((895 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-189 / 16 : ℚ) : ℝ) ≤ ((267021477129 / 144115188075855872 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_895 : ((16342589 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((895 / 8 : ℚ) : ℝ) ∧
    logKernel ((895 / 8 : ℚ) : ℝ) ≤ ((32685183 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_895
  constructor
  · exact (show ((16342589 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((34178749072509 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((895 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((267021477129 / 144115188075855872 : ℚ) : ℝ) ≤ ((32685183 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_896 : ((30162640190705 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((112 / 1 : ℚ) : ℝ) ∧
    heightZ ((112 / 1 : ℚ) : ℝ) ≤ ((7540660047677 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((30162640190705 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((112 / 1 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-191 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((112 / 1 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-191 / 16 : ℚ) : ℝ) ≤ ((7540660047677 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_896 : ((12727621 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((112 / 1 : ℚ) : ℝ) ∧
    logKernel ((112 / 1 : ℚ) : ℝ) ≤ ((25455247 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_896
  constructor
  · exact (show ((12727621 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((30162640190705 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((112 / 1 : ℚ) : ℝ)) hh).trans
      (show zKernel ((7540660047677 / 4611686018427387904 : ℚ) : ℝ) ≤ ((25455247 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_897 : ((26618436542071 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((897 / 8 : ℚ) : ℝ) ∧
    heightZ ((897 / 8 : ℚ) : ℝ) ≤ ((13309218271037 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((26618436542071 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((897 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-193 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((897 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-193 / 16 : ℚ) : ℝ) ≤ ((13309218271037 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_897 : ((9912281 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((897 / 8 : ℚ) : ℝ) ∧
    logKernel ((897 / 8 : ℚ) : ℝ) ≤ ((19824567 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_897
  constructor
  · exact (show ((9912281 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((26618436542071 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((897 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((13309218271037 / 9223372036854775808 : ℚ) : ℝ) ≤ ((19824567 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_898 : ((11745343900011 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((449 / 4 : ℚ) : ℝ) ∧
    heightZ ((449 / 4 : ℚ) : ℝ) ≤ ((23490687800025 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((11745343900011 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((449 / 4 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-195 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((449 / 4 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-195 / 16 : ℚ) : ℝ) ≤ ((23490687800025 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_898 : ((1929923 / 9007199254740992 : ℚ) : ℝ) ≤ logKernel ((449 / 4 : ℚ) : ℝ) ∧
    logKernel ((449 / 4 : ℚ) : ℝ) ≤ ((15439389 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_898
  constructor
  · exact (show ((1929923 / 9007199254740992 : ℚ) : ℝ) ≤ zKernel ((11745343900011 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((449 / 4 : ℚ) : ℝ)) hh).trans
      (show zKernel ((23490687800025 / 18446744073709551616 : ℚ) : ℝ) ≤ ((15439389 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_899 : ((20730459223101 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((899 / 8 : ℚ) : ℝ) ∧
    heightZ ((899 / 8 : ℚ) : ℝ) ≤ ((323913425361 / 288230376151711744 : ℚ) : ℝ) := by
  have h : ((20730459223101 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((899 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-197 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((899 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-197 / 16 : ℚ) : ℝ) ≤ ((323913425361 / 288230376151711744 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_899 : ((3006051 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((899 / 8 : ℚ) : ℝ) ∧
    logKernel ((899 / 8 : ℚ) : ℝ) ≤ ((12024209 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_899
  constructor
  · exact (show ((3006051 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((20730459223101 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((899 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((323913425361 / 288230376151711744 : ℚ) : ℝ) ≤ ((12024209 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_900 : ((18294566053543 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((225 / 2 : ℚ) : ℝ) ∧
    heightZ ((225 / 2 : ℚ) : ℝ) ≤ ((9147283026773 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((18294566053543 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((225 / 2 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-199 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((225 / 2 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-199 / 16 : ℚ) : ℝ) ≤ ((9147283026773 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_900 : ((9364459 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((225 / 2 : ℚ) : ℝ) ∧
    logKernel ((225 / 2 : ℚ) : ℝ) ≤ ((585279 / 4503599627370496 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_900
  constructor
  · exact (show ((9364459 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((18294566053543 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((225 / 2 : ℚ) : ℝ)) hh).trans
      (show zKernel ((9147283026773 / 9223372036854775808 : ℚ) : ℝ) ≤ ((585279 / 4503599627370496 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_901 : ((4036224469095 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((901 / 8 : ℚ) : ℝ) ∧
    heightZ ((901 / 8 : ℚ) : ℝ) ≤ ((16144897876383 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((4036224469095 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((901 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-201 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((901 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-201 / 16 : ℚ) : ℝ) ≤ ((16144897876383 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_901 : ((7293047 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((901 / 8 : ℚ) : ℝ) ∧
    logKernel ((901 / 8 : ℚ) : ℝ) ≤ ((1823263 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_901
  constructor
  · exact (show ((7293047 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((4036224469095 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((901 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((16144897876383 / 18446744073709551616 : ℚ) : ℝ) ≤ ((1823263 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_902 : ((7123911184225 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((451 / 4 : ℚ) : ℝ) ∧
    heightZ ((451 / 4 : ℚ) : ℝ) ≤ ((14247822368453 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((7123911184225 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((451 / 4 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-203 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((451 / 4 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-203 / 16 : ℚ) : ℝ) ≤ ((14247822368453 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_902 : ((2839915 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((451 / 4 : ℚ) : ℝ) ∧
    logKernel ((451 / 4 : ℚ) : ℝ) ≤ ((5679835 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_902
  constructor
  · exact (show ((2839915 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((7123911184225 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((451 / 4 : ℚ) : ℝ)) hh).trans
      (show zKernel ((14247822368453 / 18446744073709551616 : ℚ) : ℝ) ≤ ((5679835 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_903 : ((12573659108733 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((903 / 8 : ℚ) : ℝ) ∧
    heightZ ((903 / 8 : ℚ) : ℝ) ≤ ((98231711787 / 144115188075855872 : ℚ) : ℝ) := by
  have h : ((12573659108733 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((903 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-205 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((903 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-205 / 16 : ℚ) : ℝ) ≤ ((98231711787 / 144115188075855872 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_903 : ((138233 / 2251799813685248 : ℚ) : ℝ) ≤ logKernel ((903 / 8 : ℚ) : ℝ) ∧
    logKernel ((903 / 8 : ℚ) : ℝ) ≤ ((4423461 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_903
  constructor
  · exact (show ((138233 / 2251799813685248 : ℚ) : ℝ) ≤ zKernel ((12573659108733 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((903 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((98231711787 / 144115188075855872 : ℚ) : ℝ) ≤ ((4423461 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_904 : ((11096215217611 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((113 / 1 : ℚ) : ℝ) ∧
    heightZ ((113 / 1 : ℚ) : ℝ) ≤ ((5548107608807 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((11096215217611 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((113 / 1 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-207 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((113 / 1 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-207 / 16 : ℚ) : ℝ) ≤ ((5548107608807 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_904 : ((1722495 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((113 / 1 : ℚ) : ℝ) ∧
    logKernel ((113 / 1 : ℚ) : ℝ) ≤ ((3444995 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_904
  constructor
  · exact (show ((1722495 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((11096215217611 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((113 / 1 : ℚ) : ℝ)) hh).trans
      (show zKernel ((5548107608807 / 9223372036854775808 : ℚ) : ℝ) ≤ ((3444995 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_905 : ((4896187779977 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((905 / 8 : ℚ) : ℝ) ∧
    heightZ ((905 / 8 : ℚ) : ℝ) ≤ ((9792375559957 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((4896187779977 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((905 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-209 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((905 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-209 / 16 : ℚ) : ℝ) ≤ ((9792375559957 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_905 : ((2682961 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((905 / 8 : ℚ) : ℝ) ∧
    logKernel ((905 / 8 : ℚ) : ℝ) ≤ ((1341483 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_905
  constructor
  · exact (show ((2682961 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((4896187779977 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((905 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((9792375559957 / 18446744073709551616 : ℚ) : ℝ) ≤ ((1341483 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_906 : ((2160435275151 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((453 / 4 : ℚ) : ℝ) ∧
    heightZ ((453 / 4 : ℚ) : ℝ) ≤ ((8641741100607 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((2160435275151 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((453 / 4 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-211 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((453 / 4 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-211 / 16 : ℚ) : ℝ) ≤ ((8641741100607 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_906 : ((2089491 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((453 / 4 : ℚ) : ℝ) ∧
    logKernel ((453 / 4 : ℚ) : ℝ) ≤ ((261187 / 9007199254740992 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_906
  constructor
  · exact (show ((2089491 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((2160435275151 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((453 / 4 : ℚ) : ℝ)) hh).trans
      (show zKernel ((8641741100607 / 18446744073709551616 : ℚ) : ℝ) ≤ ((261187 / 9007199254740992 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_907 : ((7626309754221 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((907 / 8 : ℚ) : ℝ) ∧
    heightZ ((907 / 8 : ℚ) : ℝ) ≤ ((476644359639 / 1152921504606846976 : ℚ) : ℝ) := by
  have h : ((7626309754221 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((907 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-213 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((907 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-213 / 16 : ℚ) : ℝ) ≤ ((476644359639 / 1152921504606846976 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_907 : ((1627297 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((907 / 8 : ℚ) : ℝ) ∧
    logKernel ((907 / 8 : ℚ) : ℝ) ≤ ((813651 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_907
  constructor
  · exact (show ((1627297 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((7626309754221 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((907 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((476644359639 / 1152921504606846976 : ℚ) : ℝ) ≤ ((813651 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_908 : ((3365097368125 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((227 / 2 : ℚ) : ℝ) ∧
    heightZ ((227 / 2 : ℚ) : ℝ) ≤ ((6730194736253 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((3365097368125 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((227 / 2 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-215 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((227 / 2 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-215 / 16 : ℚ) : ℝ) ≤ ((6730194736253 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_908 : ((1267339 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((227 / 2 : ℚ) : ℝ) ∧
    logKernel ((227 / 2 : ℚ) : ℝ) ≤ ((79209 / 4503599627370496 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_908
  constructor
  · exact (show ((1267339 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((3365097368125 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((227 / 2 : ℚ) : ℝ)) hh).trans
      (show zKernel ((6730194736253 / 18446744073709551616 : ℚ) : ℝ) ≤ ((79209 / 4503599627370496 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_909 : ((1484844002133 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((909 / 8 : ℚ) : ℝ) ∧
    heightZ ((909 / 8 : ℚ) : ℝ) ≤ ((5939376008535 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((1484844002133 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((909 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-217 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((909 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-217 / 16 : ℚ) : ℝ) ≤ ((5939376008535 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_909 : ((246751 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((909 / 8 : ℚ) : ℝ) ∧
    logKernel ((909 / 8 : ℚ) : ℝ) ≤ ((987009 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_909
  constructor
  · exact (show ((246751 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((1484844002133 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((909 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((5939376008535 / 18446744073709551616 : ℚ) : ℝ) ≤ ((987009 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_910 : ((2620740465407 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((455 / 4 : ℚ) : ℝ) ∧
    heightZ ((455 / 4 : ℚ) : ℝ) ≤ ((5241480930817 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((2620740465407 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((455 / 4 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-219 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((455 / 4 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-219 / 16 : ℚ) : ℝ) ≤ ((5241480930817 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_910 : ((768679 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((455 / 4 : ℚ) : ℝ) ∧
    logKernel ((455 / 4 : ℚ) : ℝ) ≤ ((192171 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_910
  constructor
  · exact (show ((768679 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((2620740465407 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((455 / 4 : ℚ) : ℝ)) hh).trans
      (show zKernel ((5241480930817 / 18446744073709551616 : ℚ) : ℝ) ≤ ((192171 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_911 : ((72274854475 / 288230376151711744 : ℚ) : ℝ) ≤ heightZ ((911 / 8 : ℚ) : ℝ) ∧
    heightZ ((911 / 8 : ℚ) : ℝ) ≤ ((4625590686403 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((72274854475 / 288230376151711744 : ℚ) : ℝ) ≤ Real.exp (-((911 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-221 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((911 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-221 / 16 : ℚ) : ℝ) ≤ ((4625590686403 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_911 : ((598647 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((911 / 8 : ℚ) : ℝ) ∧
    logKernel ((911 / 8 : ℚ) : ℝ) ≤ ((149663 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_911
  constructor
  · exact (show ((598647 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((72274854475 / 288230376151711744 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((911 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((4625590686403 / 18446744073709551616 : ℚ) : ℝ) ≤ ((149663 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_912 : ((1020517363343 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((114 / 1 : ℚ) : ℝ) ∧
    heightZ ((114 / 1 : ℚ) : ℝ) ≤ ((4082069453375 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((1020517363343 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((114 / 1 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-223 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((114 / 1 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-223 / 16 : ℚ) : ℝ) ≤ ((4082069453375 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_912 : ((466227 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((114 / 1 : ℚ) : ℝ) ∧
    logKernel ((114 / 1 : ℚ) : ℝ) ≤ ((58279 / 9007199254740992 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_912
  constructor
  · exact (show ((466227 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((1020517363343 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((114 / 1 : ℚ) : ℝ)) hh).trans
      (show zKernel ((4082069453375 / 18446744073709551616 : ℚ) : ℝ) ≤ ((58279 / 9007199254740992 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_913 : ((112575426523 / 576460752303423488 : ℚ) : ℝ) ≤ heightZ ((913 / 8 : ℚ) : ℝ) ∧
    heightZ ((913 / 8 : ℚ) : ℝ) ≤ ((3602413648739 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((112575426523 / 576460752303423488 : ℚ) : ℝ) ≤ Real.exp (-((913 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-225 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((913 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-225 / 16 : ℚ) : ℝ) ≤ ((3602413648739 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_913 : ((363097 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((913 / 8 : ℚ) : ℝ) ∧
    logKernel ((913 / 8 : ℚ) : ℝ) ≤ ((181551 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_913
  constructor
  · exact (show ((363097 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((112575426523 / 576460752303423488 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((913 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((3602413648739 / 18446744073709551616 : ℚ) : ℝ) ≤ ((181551 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_914 : ((1589559443419 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((457 / 4 : ℚ) : ℝ) ∧
    heightZ ((457 / 4 : ℚ) : ℝ) ≤ ((3179118886841 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((1589559443419 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((457 / 4 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-227 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((457 / 4 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-227 / 16 : ℚ) : ℝ) ≤ ((3179118886841 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_914 : ((70695 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((457 / 4 : ℚ) : ℝ) ∧
    logKernel ((457 / 4 : ℚ) : ℝ) ≤ ((282785 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_914
  constructor
  · exact (show ((70695 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((1589559443419 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((457 / 4 : ℚ) : ℝ)) hh).trans
      (show zKernel ((3179118886841 / 18446744073709551616 : ℚ) : ℝ) ≤ ((282785 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_915 : ((1402781285291 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((915 / 8 : ℚ) : ℝ) ∧
    heightZ ((915 / 8 : ℚ) : ℝ) ≤ ((2805562570585 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((1402781285291 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((915 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-229 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((915 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-229 / 16 : ℚ) : ℝ) ≤ ((2805562570585 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_915 : ((220229 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((915 / 8 : ℚ) : ℝ) ∧
    logKernel ((915 / 8 : ℚ) : ℝ) ≤ ((110117 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_915
  constructor
  · exact (show ((220229 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((1402781285291 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((915 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((2805562570585 / 18446744073709551616 : ℚ) : ℝ) ≤ ((110117 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_916 : ((1237950139273 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((229 / 2 : ℚ) : ℝ) ∧
    heightZ ((229 / 2 : ℚ) : ℝ) ≤ ((2475900278549 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((1237950139273 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((229 / 2 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-231 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((229 / 2 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-231 / 16 : ℚ) : ℝ) ≤ ((2475900278549 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_916 : ((85757 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((229 / 2 : ℚ) : ℝ) ∧
    logKernel ((229 / 2 : ℚ) : ℝ) ≤ ((171519 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_916
  constructor
  · exact (show ((85757 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((1237950139273 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((229 / 2 : ℚ) : ℝ)) hh).trans
      (show zKernel ((2475900278549 / 18446744073709551616 : ℚ) : ℝ) ≤ ((171519 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_917 : ((2184974326925 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((917 / 8 : ℚ) : ℝ) ∧
    heightZ ((917 / 8 : ℚ) : ℝ) ≤ ((136560895433 / 1152921504606846976 : ℚ) : ℝ) := by
  have h : ((2184974326925 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((917 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-233 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((917 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-233 / 16 : ℚ) : ℝ) ≤ ((136560895433 / 1152921504606846976 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_917 : ((66787 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((917 / 8 : ℚ) : ℝ) ∧
    logKernel ((917 / 8 : ℚ) : ℝ) ≤ ((133579 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_917
  constructor
  · exact (show ((66787 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((2184974326925 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((917 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((136560895433 / 1152921504606846976 : ℚ) : ℝ) ≤ ((133579 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_918 : ((964116537869 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((459 / 4 : ℚ) : ℝ) ∧
    heightZ ((459 / 4 : ℚ) : ℝ) ≤ ((1928233075741 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((964116537869 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((459 / 4 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-235 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((459 / 4 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-235 / 16 : ℚ) : ℝ) ≤ ((1928233075741 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_918 : ((104027 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((459 / 4 : ℚ) : ℝ) ∧
    logKernel ((459 / 4 : ℚ) : ℝ) ≤ ((3251 / 2251799813685248 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_918
  constructor
  · exact (show ((104027 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((964116537869 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((459 / 4 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1928233075741 / 18446744073709551616 : ℚ) : ℝ) ≤ ((3251 / 2251799813685248 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_919 : ((26588433075 / 288230376151711744 : ℚ) : ℝ) ≤ heightZ ((919 / 8 : ℚ) : ℝ) ∧
    heightZ ((919 / 8 : ℚ) : ℝ) ≤ ((1701659716803 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((26588433075 / 288230376151711744 : ℚ) : ℝ) ≤ Real.exp (-((919 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-237 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((919 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-237 / 16 : ℚ) : ℝ) ≤ ((1701659716803 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_919 : ((10127 / 9007199254740992 : ℚ) : ℝ) ≤ logKernel ((919 / 8 : ℚ) : ℝ) ∧
    logKernel ((919 / 8 : ℚ) : ℝ) ≤ ((81021 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_919
  constructor
  · exact (show ((10127 / 9007199254740992 : ℚ) : ℝ) ≤ zKernel ((26588433075 / 288230376151711744 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((919 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1701659716803 / 18446744073709551616 : ℚ) : ℝ) ≤ ((81021 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_920 : ((93856839333 / 1152921504606846976 : ℚ) : ℝ) ≤ heightZ ((115 / 1 : ℚ) : ℝ) ∧
    heightZ ((115 / 1 : ℚ) : ℝ) ≤ ((1501709429331 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((93856839333 / 1152921504606846976 : ℚ) : ℝ) ≤ Real.exp (-((115 / 1 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-239 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((115 / 1 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-239 / 16 : ℚ) : ℝ) ≤ ((1501709429331 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_920 : ((63095 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((115 / 1 : ℚ) : ℝ) ∧
    logKernel ((115 / 1 : ℚ) : ℝ) ≤ ((15775 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_920
  constructor
  · exact (show ((63095 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((93856839333 / 1152921504606846976 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((115 / 1 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1501709429331 / 18446744073709551616 : ℚ) : ℝ) ≤ ((15775 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem log_height_bounds_96 : ((169840635127947007 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((223 / 2 : ℚ) : ℝ) ∧
    Real.log ((223 / 2 : ℚ) : ℝ) ≤ ((339681270255894017 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((169840635127947007 / 36028797018963968 : ℚ) : ℝ) ≤ ((223 / 2 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((223 / 2 : ℚ) : ℝ) ≤ Real.exp ((339681270255894017 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_96 : heightPower (96 : Fin 125) ≤ ((3437942287267007 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_96
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_96 : heightFactor (96 : Fin 125) ≤ ((27981691477 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_96
  obtain ⟨hpl, hph⟩ := kernel_bounds_891
  obtain ⟨hcl, hch⟩ := kernel_bounds_892
  obtain ⟨hzl, hzh⟩ := height_z_bounds_892
  have h : (((49729 / 2 : ℚ) : ℝ) * (logKernel ((891 / 8 : ℚ) : ℝ) - logKernel ((223 / 2 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((223 / 2 : ℚ) : ℝ) + Real.log ((223 / 2 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((27981691477 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_97 : ((339762007064382955 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((893 / 8 : ℚ) : ℝ) ∧
    Real.log ((893 / 8 : ℚ) : ℝ) ≤ ((169881003532191479 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((339762007064382955 / 72057594037927936 : ℚ) : ℝ) ≤ ((893 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((893 / 8 : ℚ) : ℝ) ≤ Real.exp ((169881003532191479 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_97 : heightPower (97 : Fin 125) ≤ ((3473442037513999 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_97
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_97 : heightFactor (97 : Fin 125) ≤ ((5694718949 / 17592186044416 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_97
  obtain ⟨hpl, hph⟩ := kernel_bounds_892
  obtain ⟨hcl, hch⟩ := kernel_bounds_893
  obtain ⟨hzl, hzh⟩ := height_z_bounds_893
  have h : (((797449 / 32 : ℚ) : ℝ) * (logKernel ((223 / 2 : ℚ) : ℝ) - logKernel ((893 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((893 / 8 : ℚ) : ℝ) + Real.log ((893 / 8 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((5694718949 / 17592186044416 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_98 : ((339842653512686833 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((447 / 4 : ℚ) : ℝ) ∧
    Real.log ((447 / 4 : ℚ) : ℝ) ≤ ((84960663378171709 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((339842653512686833 / 72057594037927936 : ℚ) : ℝ) ≤ ((447 / 4 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((447 / 4 : ℚ) : ℝ) ≤ Real.exp ((84960663378171709 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_98 : heightPower (98 : Fin 125) ≤ ((1754470717395759 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_98
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_98 : heightFactor (98 : Fin 125) ≤ ((18543407869 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_98
  obtain ⟨hpl, hph⟩ := kernel_bounds_893
  obtain ⟨hcl, hch⟩ := kernel_bounds_894
  obtain ⟨hzl, hzh⟩ := height_z_bounds_894
  have h : (((199809 / 8 : ℚ) : ℝ) * (logKernel ((893 / 8 : ℚ) : ℝ) - logKernel ((447 / 4 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((447 / 4 : ℚ) : ℝ) + Real.log ((447 / 4 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((18543407869 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_99 : ((339923209802840781 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((895 / 8 : ℚ) : ℝ) ∧
    Real.log ((895 / 8 : ℚ) : ℝ) ≤ ((21245200612677549 / 4503599627370496 : ℚ) : ℝ) := by
  have hl : Real.exp ((339923209802840781 / 72057594037927936 : ℚ) : ℝ) ≤ ((895 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((895 / 8 : ℚ) : ℝ) ≤ Real.exp ((21245200612677549 / 4503599627370496 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_99 : heightPower (99 : Fin 125) ≤ ((886110119972191 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_99
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_99 : heightFactor (99 : Fin 125) ≤ ((60381764415 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_99
  obtain ⟨hpl, hph⟩ := kernel_bounds_894
  obtain ⟨hcl, hch⟩ := kernel_bounds_895
  obtain ⟨hzl, hzh⟩ := height_z_bounds_895
  have h : (((801025 / 32 : ℚ) : ℝ) * (logKernel ((447 / 4 : ℚ) : ℝ) - logKernel ((895 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((895 / 8 : ℚ) : ℝ) + Real.log ((895 / 8 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((60381764415 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_100 : ((170001838068101549 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((112 / 1 : ℚ) : ℝ) ∧
    Real.log ((112 / 1 : ℚ) : ℝ) ≤ ((340003676136203101 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((170001838068101549 / 36028797018963968 : ℚ) : ℝ) ≤ ((112 / 1 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((112 / 1 : ℚ) : ℝ) ≤ Real.exp ((340003676136203101 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_100 : heightPower (100 : Fin 125) ≤ ((3579939173592293 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_100
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_100 : heightFactor (100 : Fin 125) ≤ ((49154254283 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_100
  obtain ⟨hpl, hph⟩ := kernel_bounds_895
  obtain ⟨hcl, hch⟩ := kernel_bounds_896
  obtain ⟨hzl, hzh⟩ := height_z_bounds_896
  have h : (((25088 / 1 : ℚ) : ℝ) * (logKernel ((895 / 8 : ℚ) : ℝ) - logKernel ((112 / 1 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((112 / 1 : ℚ) : ℝ) + Real.log ((112 / 1 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((49154254283 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_101 : ((85021013178364567 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((897 / 8 : ℚ) : ℝ) ∧
    Real.log ((897 / 8 : ℚ) : ℝ) ≤ ((340084052713458271 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((85021013178364567 / 18014398509481984 : ℚ) : ℝ) ≤ ((897 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((897 / 8 : ℚ) : ℝ) ≤ Real.exp ((340084052713458271 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_101 : heightPower (101 : Fin 125) ≤ ((903859379171507 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_101
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_101 : heightFactor (101 : Fin 125) ≤ ((625223915 / 4398046511104 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_101
  obtain ⟨hpl, hph⟩ := kernel_bounds_896
  obtain ⟨hcl, hch⟩ := kernel_bounds_897
  obtain ⟨hzl, hzh⟩ := height_z_bounds_897
  have h : (((804609 / 32 : ℚ) : ℝ) * (logKernel ((112 / 1 : ℚ) : ℝ) - logKernel ((897 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((897 / 8 : ℚ) : ℝ) + Real.log ((897 / 8 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((625223915 / 4398046511104 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_102 : ((340164339734619961 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((449 / 4 : ℚ) : ℝ) ∧
    Real.log ((449 / 4 : ℚ) : ℝ) ≤ ((85041084933654991 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((340164339734619961 / 72057594037927936 : ℚ) : ℝ) ≤ ((449 / 4 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((449 / 4 : ℚ) : ℝ) ≤ Real.exp ((85041084933654991 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_102 : heightPower (102 : Fin 125) ≤ ((3650935509951273 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_102
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_102 : heightFactor (102 : Fin 125) ≤ ((4071732479 / 35184372088832 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_102
  obtain ⟨hpl, hph⟩ := kernel_bounds_897
  obtain ⟨hcl, hch⟩ := kernel_bounds_898
  obtain ⟨hzl, hzh⟩ := height_z_bounds_898
  have h : (((201601 / 8 : ℚ) : ℝ) * (logKernel ((897 / 8 : ℚ) : ℝ) - logKernel ((449 / 4 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((449 / 4 : ℚ) : ℝ) + Real.log ((449 / 4 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((4071732479 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_103 : ((340244537399034023 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((899 / 8 : ℚ) : ℝ) ∧
    Real.log ((899 / 8 : ℚ) : ℝ) ≤ ((170122268699517013 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((340244537399034023 / 72057594037927936 : ℚ) : ℝ) ≤ ((899 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((899 / 8 : ℚ) : ℝ) ≤ Real.exp ((170122268699517013 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_103 : heightPower (103 : Fin 125) ≤ ((1843216577083361 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_103
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_103 : heightFactor (103 : Fin 125) ≤ ((26516868087 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_103
  obtain ⟨hpl, hph⟩ := kernel_bounds_898
  obtain ⟨hcl, hch⟩ := kernel_bounds_899
  obtain ⟨hzl, hzh⟩ := height_z_bounds_899
  have h : (((808201 / 32 : ℚ) : ℝ) * (logKernel ((449 / 4 : ℚ) : ℝ) - logKernel ((899 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((899 / 8 : ℚ) : ℝ) + Real.log ((899 / 8 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((26516868087 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_104 : ((340324645905381445 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((225 / 2 : ℚ) : ℝ) ∧
    Real.log ((225 / 2 : ℚ) : ℝ) ≤ ((42540580738172681 / 9007199254740992 : ℚ) : ℝ) := by
  have hl : Real.exp ((340324645905381445 / 72057594037927936 : ℚ) : ℝ) ≤ ((225 / 2 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((225 / 2 : ℚ) : ℝ) ≤ Real.exp ((42540580738172681 / 9007199254740992 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_104 : heightPower (104 : Fin 125) ≤ ((1860965225054237 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_104
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_104 : heightFactor (104 : Fin 125) ≤ ((10793063025 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_104
  obtain ⟨hpl, hph⟩ := kernel_bounds_899
  obtain ⟨hcl, hch⟩ := kernel_bounds_900
  obtain ⟨hzl, hzh⟩ := height_z_bounds_900
  have h : (((50625 / 2 : ℚ) : ℝ) * (logKernel ((899 / 8 : ℚ) : ℝ) - logKernel ((225 / 2 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((225 / 2 : ℚ) : ℝ) + Real.log ((225 / 2 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((10793063025 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_105 : ((170202332725840657 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((901 / 8 : ℚ) : ℝ) ∧
    Real.log ((901 / 8 : ℚ) : ℝ) ≤ ((340404665451681317 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((170202332725840657 / 36028797018963968 : ℚ) : ℝ) ≤ ((901 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((901 / 8 : ℚ) : ℝ) ≤ Real.exp ((340404665451681317 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_105 : heightPower (105 : Fin 125) ≤ ((469678424818755 / 35184372088832 : ℚ) : ℝ) := by
  have hh := log_height_bounds_105
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_105 : heightFactor (105 : Fin 125) ≤ ((4393057049 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_105
  obtain ⟨hpl, hph⟩ := kernel_bounds_900
  obtain ⟨hcl, hch⟩ := kernel_bounds_901
  obtain ⟨hzl, hzh⟩ := height_z_bounds_901
  have h : (((811801 / 32 : ℚ) : ℝ) * (logKernel ((225 / 2 : ℚ) : ℝ) - logKernel ((901 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((901 / 8 : ℚ) : ℝ) + Real.log ((901 / 8 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((4393057049 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_106 : ((42560574529411719 / 9007199254740992 : ℚ) : ℝ) ≤ Real.log ((451 / 4 : ℚ) : ℝ) ∧
    Real.log ((451 / 4 : ℚ) : ℝ) ≤ ((340484596235293755 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((42560574529411719 / 9007199254740992 : ℚ) : ℝ) ≤ ((451 / 4 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((451 / 4 : ℚ) : ℝ) ≤ Real.exp ((340484596235293755 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_106 : heightPower (106 : Fin 125) ≤ ((1896462000131179 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_106
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_106 : heightFactor (106 : Fin 125) ≤ ((7152350965 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_106
  obtain ⟨hpl, hph⟩ := kernel_bounds_901
  obtain ⟨hcl, hch⟩ := kernel_bounds_902
  obtain ⟨hzl, hzh⟩ := height_z_bounds_902
  have h : (((203401 / 8 : ℚ) : ℝ) * (logKernel ((901 / 8 : ℚ) : ℝ) - logKernel ((451 / 4 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((451 / 4 : ℚ) : ℝ) + Real.log ((451 / 4 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((7152350965 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_107 : ((340564438452922835 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((903 / 8 : ℚ) : ℝ) ∧
    Real.log ((903 / 8 : ℚ) : ℝ) ≤ ((170282219226461419 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((340564438452922835 / 72057594037927936 : ℚ) : ℝ) ≤ ((903 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((903 / 8 : ℚ) : ℝ) ≤ Real.exp ((170282219226461419 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_107 : heightPower (107 : Fin 125) ≤ ((3828420256013803 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_107
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_107 : heightFactor (107 : Fin 125) ≤ ((5822384771 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_107
  obtain ⟨hpl, hph⟩ := kernel_bounds_902
  obtain ⟨hcl, hch⟩ := kernel_bounds_903
  obtain ⟨hzl, hzh⟩ := height_z_bounds_903
  have h : (((815409 / 32 : ℚ) : ℝ) * (logKernel ((451 / 4 : ℚ) : ℝ) - logKernel ((903 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((903 / 8 : ℚ) : ℝ) + Real.log ((903 / 8 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((5822384771 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_108 : ((340644192300619501 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((113 / 1 : ℚ) : ℝ) ∧
    Real.log ((113 / 1 : ℚ) : ℝ) ≤ ((21290262018788719 / 4503599627370496 : ℚ) : ℝ) := by
  have hl : Real.exp ((340644192300619501 / 72057594037927936 : ℚ) : ℝ) ≤ ((113 / 1 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((113 / 1 : ℚ) : ℝ) ≤ Real.exp ((21290262018788719 / 4503599627370496 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_108 : heightPower (108 : Fin 125) ≤ ((482989520821275 / 35184372088832 : ℚ) : ℝ) := by
  have hh := log_height_bounds_108
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_108 : heightFactor (108 : Fin 125) ≤ ((2369863927 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_108
  obtain ⟨hpl, hph⟩ := kernel_bounds_903
  obtain ⟨hcl, hch⟩ := kernel_bounds_904
  obtain ⟨hzl, hzh⟩ := height_z_bounds_904
  have h : (((25538 / 1 : ℚ) : ℝ) * (logKernel ((903 / 8 : ℚ) : ℝ) - logKernel ((113 / 1 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((113 / 1 : ℚ) : ℝ) + Real.log ((113 / 1 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((2369863927 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_109 : ((340723857973784433 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((905 / 8 : ℚ) : ℝ) ∧
    Real.log ((905 / 8 : ℚ) : ℝ) ≤ ((85180964493446109 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((340723857973784433 / 72057594037927936 : ℚ) : ℝ) ≤ ((905 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((905 / 8 : ℚ) : ℝ) ≤ Real.exp ((85180964493446109 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_109 : heightPower (109 : Fin 125) ≤ ((3899411732694833 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_109
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_109 : heightFactor (109 : Fin 125) ≤ ((7716790435 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_109
  obtain ⟨hpl, hph⟩ := kernel_bounds_904
  obtain ⟨hcl, hch⟩ := kernel_bounds_905
  obtain ⟨hzl, hzh⟩ := height_z_bounds_905
  have h : (((819025 / 32 : ℚ) : ℝ) * (logKernel ((113 / 1 : ℚ) : ℝ) - logKernel ((905 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((905 / 8 : ℚ) : ℝ) + Real.log ((905 / 8 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((7716790435 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_110 : ((42600429458396367 / 9007199254740992 : ℚ) : ℝ) ≤ Real.log ((453 / 4 : ℚ) : ℝ) ∧
    Real.log ((453 / 4 : ℚ) : ℝ) ≤ ((340803435667170939 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((42600429458396367 / 9007199254740992 : ℚ) : ℝ) ≤ ((453 / 4 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((453 / 4 : ℚ) : ℝ) ≤ Real.exp ((340803435667170939 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_110 : heightPower (110 : Fin 125) ≤ ((491863369393557 / 35184372088832 : ℚ) : ℝ) := by
  have hh := log_height_bounds_110
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_110 : heightFactor (110 : Fin 125) ≤ ((6281903787 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_110
  obtain ⟨hpl, hph⟩ := kernel_bounds_905
  obtain ⟨hcl, hch⟩ := kernel_bounds_906
  obtain ⟨hzl, hzh⟩ := height_z_bounds_906
  have h : (((205209 / 8 : ℚ) : ℝ) * (logKernel ((905 / 8 : ℚ) : ℝ) - logKernel ((453 / 4 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((453 / 4 : ℚ) : ℝ) + Real.log ((453 / 4 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((6281903787 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_111 : ((340882925574887791 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((907 / 8 : ℚ) : ℝ) ∧
    Real.log ((907 / 8 : ℚ) : ℝ) ≤ ((170441462787443897 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((340882925574887791 / 72057594037927936 : ℚ) : ℝ) ≤ ((907 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((907 / 8 : ℚ) : ℝ) ≤ Real.exp ((170441462787443897 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_111 : heightPower (111 : Fin 125) ≤ ((3970401834689307 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_111
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_111 : heightFactor (111 : Fin 125) ≤ ((5113846641 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_111
  obtain ⟨hpl, hph⟩ := kernel_bounds_906
  obtain ⟨hcl, hch⟩ := kernel_bounds_907
  obtain ⟨hzl, hzh⟩ := height_z_bounds_907
  have h : (((822649 / 32 : ℚ) : ℝ) * (logKernel ((453 / 4 : ℚ) : ℝ) - logKernel ((907 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((907 / 8 : ℚ) : ℝ) + Real.log ((907 / 8 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((5113846641 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_112 : ((170481163945201049 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((227 / 2 : ℚ) : ℝ) ∧
    Real.log ((227 / 2 : ℚ) : ℝ) ≤ ((340962327890402101 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((170481163945201049 / 36028797018963968 : ℚ) : ℝ) ≤ ((227 / 2 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((227 / 2 : ℚ) : ℝ) ≤ Real.exp ((340962327890402101 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_112 : heightPower (112 : Fin 125) ≤ ((4005896372073117 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_112
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_112 : heightFactor (112 : Fin 125) ≤ ((2081501243 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_112
  obtain ⟨hpl, hph⟩ := kernel_bounds_907
  obtain ⟨hcl, hch⟩ := kernel_bounds_908
  obtain ⟨hzl, hzh⟩ := height_z_bounds_908
  have h : (((51529 / 2 : ℚ) : ℝ) * (logKernel ((907 / 8 : ℚ) : ℝ) - logKernel ((227 / 2 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((227 / 2 : ℚ) : ℝ) + Real.log ((227 / 2 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((2081501243 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_113 : ((85260410701635525 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((909 / 8 : ℚ) : ℝ) ∧
    Real.log ((909 / 8 : ℚ) : ℝ) ≤ ((341041642806542103 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((85260410701635525 / 18014398509481984 : ℚ) : ℝ) ≤ ((909 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((909 / 8 : ℚ) : ℝ) ≤ Real.exp ((341041642806542103 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_113 : heightPower (113 : Fin 125) ≤ ((4041390568053121 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_113
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_113 : heightFactor (113 : Fin 125) ≤ ((3388980411 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_113
  obtain ⟨hpl, hph⟩ := kernel_bounds_908
  obtain ⟨hcl, hch⟩ := kernel_bounds_909
  obtain ⟨hzl, hzh⟩ := height_z_bounds_909
  have h : (((826281 / 32 : ℚ) : ℝ) * (logKernel ((227 / 2 : ℚ) : ℝ) - logKernel ((909 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((909 / 8 : ℚ) : ℝ) + Real.log ((909 / 8 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((3388980411 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_114 : ((341120870515499991 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((455 / 4 : ℚ) : ℝ) ∧
    Real.log ((455 / 4 : ℚ) : ℝ) ≤ ((170560435257749997 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((341120870515499991 / 72057594037927936 : ℚ) : ℝ) ≤ ((455 / 4 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((455 / 4 : ℚ) : ℝ) ≤ Real.exp ((170560435257749997 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_114 : heightPower (114 : Fin 125) ≤ ((4076884423380069 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_114
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_114 : heightFactor (114 : Fin 125) ≤ ((2758899805 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_114
  obtain ⟨hpl, hph⟩ := kernel_bounds_909
  obtain ⟨hcl, hch⟩ := kernel_bounds_910
  obtain ⟨hzl, hzh⟩ := height_z_bounds_910
  have h : (((207025 / 8 : ℚ) : ℝ) * (logKernel ((909 / 8 : ℚ) : ℝ) - logKernel ((455 / 4 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((455 / 4 : ℚ) : ℝ) + Real.log ((455 / 4 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((2758899805 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_115 : ((170600005604417357 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((911 / 8 : ℚ) : ℝ) ∧
    Real.log ((911 / 8 : ℚ) : ℝ) ≤ ((341200011208834717 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((170600005604417357 / 36028797018963968 : ℚ) : ℝ) ≤ ((911 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((911 / 8 : ℚ) : ℝ) ≤ Real.exp ((341200011208834717 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_115 : heightPower (115 : Fin 125) ≤ ((64255905293785 / 4398046511104 : ℚ) : ℝ) := by
  have hh := log_height_bounds_115
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_115 : heightFactor (115 : Fin 125) ≤ ((1122996985 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_115
  obtain ⟨hpl, hph⟩ := kernel_bounds_910
  obtain ⟨hcl, hch⟩ := kernel_bounds_911
  obtain ⟨hzl, hzh⟩ := height_z_bounds_911
  have h : (((829921 / 32 : ℚ) : ℝ) * (logKernel ((455 / 4 : ℚ) : ℝ) - logKernel ((911 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((911 / 8 : ℚ) : ℝ) + Real.log ((911 / 8 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((1122996985 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_116 : ((21329941567342171 / 4503599627370496 : ℚ) : ℝ) ≤ Real.log ((114 / 1 : ℚ) : ℝ) ∧
    Real.log ((114 / 1 : ℚ) : ℝ) ≤ ((341279065077474739 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((21329941567342171 / 4503599627370496 : ℚ) : ℝ) ≤ ((114 / 1 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((114 / 1 : ℚ) : ℝ) ≤ Real.exp ((341279065077474739 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_116 : heightPower (116 : Fin 125) ≤ ((4147871115065447 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_116
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_116 : heightFactor (116 : Fin 125) ≤ ((457118337 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_116
  obtain ⟨hpl, hph⟩ := kernel_bounds_911
  obtain ⟨hcl, hch⟩ := kernel_bounds_912
  obtain ⟨hzl, hzh⟩ := height_z_bounds_912
  have h : (((25992 / 1 : ℚ) : ℝ) * (logKernel ((911 / 8 : ℚ) : ℝ) - logKernel ((114 / 1 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((114 / 1 : ℚ) : ℝ) + Real.log ((114 / 1 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((457118337 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_117 : ((21334877019482551 / 4503599627370496 : ℚ) : ℝ) ≤ Real.log ((913 / 8 : ℚ) : ℝ) ∧
    Real.log ((913 / 8 : ℚ) : ℝ) ≤ ((341358032311720819 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((21334877019482551 / 4503599627370496 : ℚ) : ℝ) ≤ ((913 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((913 / 8 : ℚ) : ℝ) ≤ Real.exp ((341358032311720819 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_117 : heightPower (117 : Fin 125) ≤ ((4183363952913053 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_117
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_117 : heightFactor (117 : Fin 125) ≤ ((1488600095 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_117
  obtain ⟨hpl, hph⟩ := kernel_bounds_912
  obtain ⟨hcl, hch⟩ := kernel_bounds_913
  obtain ⟨hzl, hzh⟩ := height_z_bounds_913
  have h : (((833569 / 32 : ℚ) : ℝ) * (logKernel ((114 / 1 : ℚ) : ℝ) - logKernel ((913 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((913 / 8 : ℚ) : ℝ) + Real.log ((913 / 8 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((1488600095 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_118 : ((170718456550624375 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((457 / 4 : ℚ) : ℝ) ∧
    Real.log ((457 / 4 : ℚ) : ℝ) ≤ ((341436913101248753 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((170718456550624375 / 36028797018963968 : ℚ) : ℝ) ≤ ((457 / 4 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((457 / 4 : ℚ) : ℝ) ≤ Real.exp ((341436913101248753 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_118 : heightPower (118 : Fin 125) ≤ ((2109428226542989 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_118
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_118 : heightFactor (118 : Fin 125) ≤ ((1211934715 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_118
  obtain ⟨hpl, hph⟩ := kernel_bounds_913
  obtain ⟨hcl, hch⟩ := kernel_bounds_914
  obtain ⟨hzl, hzh⟩ := height_z_bounds_914
  have h : (((208849 / 8 : ℚ) : ℝ) * (logKernel ((913 / 8 : ℚ) : ℝ) - logKernel ((457 / 4 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((457 / 4 : ℚ) : ℝ) + Real.log ((457 / 4 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((1211934715 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_119 : ((170757853817556053 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((915 / 8 : ℚ) : ℝ) ∧
    Real.log ((915 / 8 : ℚ) : ℝ) ≤ ((341515707635112109 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((170757853817556053 / 36028797018963968 : ℚ) : ℝ) ≤ ((915 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((915 / 8 : ℚ) : ℝ) ≤ Real.exp ((341515707635112109 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_119 : heightPower (119 : Fin 125) ≤ ((2127174308161357 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_119
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_119 : heightFactor (119 : Fin 125) ≤ ((986722771 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_119
  obtain ⟨hpl, hph⟩ := kernel_bounds_914
  obtain ⟨hcl, hch⟩ := kernel_bounds_915
  obtain ⟨hzl, hzh⟩ := height_z_bounds_915
  have h : (((837225 / 32 : ℚ) : ℝ) * (logKernel ((457 / 4 : ℚ) : ℝ) - logKernel ((915 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((915 / 8 : ℚ) : ℝ) + Real.log ((915 / 8 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((986722771 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_120 : ((341594416101744943 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((229 / 2 : ℚ) : ℝ) ∧
    Real.log ((229 / 2 : ℚ) : ℝ) ≤ ((170797208050872473 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((341594416101744943 / 72057594037927936 : ℚ) : ℝ) ≤ ((229 / 2 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((229 / 2 : ℚ) : ℝ) ≤ Real.exp ((170797208050872473 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_120 : heightPower (120 : Fin 125) ≤ ((4289840443359331 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_120
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_120 : heightFactor (120 : Fin 125) ≤ ((803395617 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_120
  obtain ⟨hpl, hph⟩ := kernel_bounds_915
  obtain ⟨hcl, hch⟩ := kernel_bounds_916
  obtain ⟨hzl, hzh⟩ := height_z_bounds_916
  have h : (((52441 / 2 : ℚ) : ℝ) * (logKernel ((915 / 8 : ℚ) : ℝ) - logKernel ((229 / 2 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((229 / 2 : ℚ) : ℝ) + Real.log ((229 / 2 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((803395617 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_121 : ((341673038688964513 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((917 / 8 : ℚ) : ℝ) ∧
    Real.log ((917 / 8 : ℚ) : ℝ) ≤ ((85418259672241129 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((341673038688964513 / 72057594037927936 : ℚ) : ℝ) ≤ ((917 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((917 / 8 : ℚ) : ℝ) ≤ Real.exp ((85418259672241129 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_121 : heightPower (121 : Fin 125) ≤ ((4325331934929489 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_121
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_121 : heightFactor (121 : Fin 125) ≤ ((163540991 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_121
  obtain ⟨hpl, hph⟩ := kernel_bounds_916
  obtain ⟨hcl, hch⟩ := kernel_bounds_917
  obtain ⟨hzl, hzh⟩ := height_z_bounds_917
  have h : (((840889 / 32 : ℚ) : ℝ) * (logKernel ((229 / 2 : ℚ) : ℝ) - logKernel ((917 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((917 / 8 : ℚ) : ℝ) + Real.log ((917 / 8 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((163540991 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_122 : ((341751575583973953 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((459 / 4 : ℚ) : ℝ) ∧
    Real.log ((459 / 4 : ℚ) : ℝ) ≤ ((85437893895993489 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((341751575583973953 / 72057594037927936 : ℚ) : ℝ) ≤ ((459 / 4 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((459 / 4 : ℚ) : ℝ) ≤ Real.exp ((85437893895993489 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_122 : heightPower (122 : Fin 125) ≤ ((1090205772941113 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_122
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_122 : heightFactor (122 : Fin 125) ≤ ((532687013 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_122
  obtain ⟨hpl, hph⟩ := kernel_bounds_917
  obtain ⟨hcl, hch⟩ := kernel_bounds_918
  obtain ⟨hzl, hzh⟩ := height_z_bounds_918
  have h : (((210681 / 8 : ℚ) : ℝ) * (logKernel ((917 / 8 : ℚ) : ℝ) - logKernel ((459 / 4 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((459 / 4 : ℚ) : ℝ) + Real.log ((459 / 4 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((532687013 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_123 : ((170915013486682479 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((919 / 8 : ℚ) : ℝ) ∧
    Real.log ((919 / 8 : ℚ) : ℝ) ≤ ((341830026973364961 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((170915013486682479 / 36028797018963968 : ℚ) : ℝ) ≤ ((919 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((919 / 8 : ℚ) : ℝ) ≤ Real.exp ((341830026973364961 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_123 : heightPower (123 : Fin 125) ≤ ((1099078478648273 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_123
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_123 : heightFactor (123 : Fin 125) ≤ ((433803109 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_123
  obtain ⟨hpl, hph⟩ := kernel_bounds_918
  obtain ⟨hcl, hch⟩ := kernel_bounds_919
  obtain ⟨hzl, hzh⟩ := height_z_bounds_919
  have h : (((844561 / 32 : ℚ) : ℝ) * (logKernel ((459 / 4 : ℚ) : ℝ) - logKernel ((919 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((919 / 8 : ℚ) : ℝ) + Real.log ((919 / 8 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((433803109 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_124 : ((170954196521560219 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((115 / 1 : ℚ) : ℝ) ∧
    Real.log ((115 / 1 : ℚ) : ℝ) ≤ ((341908393043120441 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((170954196521560219 / 36028797018963968 : ℚ) : ℝ) ≤ ((115 / 1 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((115 / 1 : ℚ) : ℝ) ≤ Real.exp ((341908393043120441 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_124 : heightPower (124 : Fin 125) ≤ ((4431804404141907 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_124
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_124 : heightFactor (124 : Fin 125) ≤ ((5049318911 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_124
  obtain ⟨hpl, hph⟩ := kernel_bounds_919
  obtain ⟨hcl, hch⟩ := kernel_bounds_920
  obtain ⟨hzl, hzh⟩ := height_z_bounds_920
  have h : (((26450 / 1 : ℚ) : ℝ) * (logKernel ((919 / 8 : ℚ) : ℝ) - logKernel ((115 / 1 : ℚ) : ℝ)) + ((1733427200 / 31 : ℚ) : ℝ) * (heightZ ((115 / 1 : ℚ) : ℝ)) ^ 2) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((115 / 1 : ℚ) : ℝ) + Real.log ((115 / 1 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((5049318911 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

end LegendreK6.M3Far.Enclosures.Height003
