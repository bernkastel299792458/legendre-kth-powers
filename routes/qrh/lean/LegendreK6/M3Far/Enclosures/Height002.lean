import LegendreK6.M3FarDefinitions
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp

/-! Generated proposals: every bound is checked by Lean, not by trusting Arb. -/
namespace LegendreK6.M3Far.Enclosures.Height002
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem height_z_bounds_859 : ((3076672942947763 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((859 / 8 : ℚ) : ℝ) ∧
    heightZ ((859 / 8 : ℚ) : ℝ) ≤ ((1538336471473883 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((3076672942947763 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((859 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-117 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((859 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-117 / 16 : ℚ) : ℝ) ≤ ((1538336471473883 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_859 : ((264850764465 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((859 / 8 : ℚ) : ℝ) ∧
    logKernel ((859 / 8 : ℚ) : ℝ) ≤ ((132425382235 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_859
  constructor
  · exact (show ((264850764465 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((3076672942947763 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((859 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1538336471473883 / 9223372036854775808 : ℚ) : ℝ) ≤ ((132425382235 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_860 : ((169697146401077 / 1152921504606846976 : ℚ) : ℝ) ≤ heightZ ((215 / 2 : ℚ) : ℝ) ∧
    heightZ ((215 / 2 : ℚ) : ℝ) ≤ ((2715154342417235 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((169697146401077 / 1152921504606846976 : ℚ) : ℝ) ≤ Real.exp (-((215 / 2 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-119 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((215 / 2 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-119 / 16 : ℚ) : ℝ) ≤ ((2715154342417235 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_860 : ((103132991381 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((215 / 2 : ℚ) : ℝ) ∧
    logKernel ((215 / 2 : ℚ) : ℝ) ≤ ((206265982767 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_860
  constructor
  · exact (show ((103132991381 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((169697146401077 / 1152921504606846976 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((215 / 2 : ℚ) : ℝ)) hh).trans
      (show zKernel ((2715154342417235 / 18446744073709551616 : ℚ) : ℝ) ≤ ((206265982767 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_861 : ((2396115297222321 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((861 / 8 : ℚ) : ℝ) ∧
    heightZ ((861 / 8 : ℚ) : ℝ) ≤ ((599028824305581 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((2396115297222321 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((861 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-121 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((861 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-121 / 16 : ℚ) : ℝ) ≤ ((599028824305581 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_861 : ((5020003403 / 2251799813685248 : ℚ) : ℝ) ≤ logKernel ((861 / 8 : ℚ) : ℝ) ∧
    logKernel ((861 / 8 : ℚ) : ℝ) ≤ ((160640108901 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_861
  constructor
  · exact (show ((5020003403 / 2251799813685248 : ℚ) : ℝ) ≤ zKernel ((2396115297222321 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((861 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((599028824305581 / 4611686018427387904 : ℚ) : ℝ) ≤ ((160640108901 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_862 : ((2114564328034265 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((431 / 4 : ℚ) : ℝ) ∧
    heightZ ((431 / 4 : ℚ) : ℝ) ≤ ((528641082008567 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((2114564328034265 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((431 / 4 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-123 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((431 / 4 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-123 / 16 : ℚ) : ℝ) ≤ ((528641082008567 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_862 : ((15638330325 / 9007199254740992 : ℚ) : ℝ) ≤ logKernel ((431 / 4 : ℚ) : ℝ) ∧
    logKernel ((431 / 4 : ℚ) : ℝ) ≤ ((125106642605 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_862
  constructor
  · exact (show ((15638330325 / 9007199254740992 : ℚ) : ℝ) ≤ zKernel ((2114564328034265 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((431 / 4 : ℚ) : ℝ)) hh).trans
      (show zKernel ((528641082008567 / 4611686018427387904 : ℚ) : ℝ) ≤ ((125106642605 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_863 : ((1866096469806115 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((863 / 8 : ℚ) : ℝ) ∧
    heightZ ((863 / 8 : ℚ) : ℝ) ≤ ((933048234903059 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((1866096469806115 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((863 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-125 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((863 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-125 / 16 : ℚ) : ℝ) ≤ ((933048234903059 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_863 : ((12179143903 / 9007199254740992 : ℚ) : ℝ) ≤ logKernel ((863 / 8 : ℚ) : ℝ) ∧
    logKernel ((863 / 8 : ℚ) : ℝ) ≤ ((97433151229 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_863
  constructor
  · exact (show ((12179143903 / 9007199254740992 : ℚ) : ℝ) ≤ zKernel ((1866096469806115 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((863 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((933048234903059 / 9223372036854775808 : ℚ) : ℝ) ≤ ((97433151229 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_864 : ((1646824354527945 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((108 / 1 : ℚ) : ℝ) ∧
    heightZ ((108 / 1 : ℚ) : ℝ) ≤ ((411706088631987 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((1646824354527945 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((108 / 1 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-127 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((108 / 1 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-127 / 16 : ℚ) : ℝ) ≤ ((411706088631987 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_864 : ((37940507235 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((108 / 1 : ℚ) : ℝ) ∧
    logKernel ((108 / 1 : ℚ) : ℝ) ≤ ((75881014475 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_864
  constructor
  · exact (show ((37940507235 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((1646824354527945 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((108 / 1 : ℚ) : ℝ)) hh).trans
      (show zKernel ((411706088631987 / 4611686018427387904 : ℚ) : ℝ) ≤ ((75881014475 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_865 : ((1453317391971787 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((865 / 8 : ℚ) : ℝ) ∧
    heightZ ((865 / 8 : ℚ) : ℝ) ≤ ((726658695985895 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((1453317391971787 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((865 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-129 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((865 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-129 / 16 : ℚ) : ℝ) ≤ ((726658695985895 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_865 : ((59096193489 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((865 / 8 : ℚ) : ℝ) ∧
    logKernel ((865 / 8 : ℚ) : ℝ) ≤ ((29548096747 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_865
  constructor
  · exact (show ((59096193489 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((1453317391971787 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((865 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((726658695985895 / 9223372036854775808 : ℚ) : ℝ) ≤ ((29548096747 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_866 : ((10019907006933 / 144115188075855872 : ℚ) : ℝ) ≤ heightZ ((433 / 4 : ℚ) : ℝ) ∧
    heightZ ((433 / 4 : ℚ) : ℝ) ≤ ((1282548096887427 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((10019907006933 / 144115188075855872 : ℚ) : ℝ) ≤ Real.exp (-((433 / 4 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-131 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((433 / 4 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-131 / 16 : ℚ) : ℝ) ≤ ((1282548096887427 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_866 : ((46024161765 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((433 / 4 : ℚ) : ℝ) ∧
    logKernel ((433 / 4 : ℚ) : ℝ) ≤ ((23012080885 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_866
  constructor
  · exact (show ((46024161765 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((10019907006933 / 144115188075855872 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((433 / 4 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1282548096887427 / 18446744073709551616 : ℚ) : ℝ) ≤ ((23012080885 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_867 : ((1131844722918919 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((867 / 8 : ℚ) : ℝ) ∧
    heightZ ((867 / 8 : ℚ) : ℝ) ≤ ((565922361459461 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((1131844722918919 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((867 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-133 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((867 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-133 / 16 : ℚ) : ℝ) ≤ ((565922361459461 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_867 : ((17921826611 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((867 / 8 : ℚ) : ℝ) ∧
    logKernel ((867 / 8 : ℚ) : ℝ) ≤ ((35843653227 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_867
  constructor
  · exact (show ((17921826611 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((1131844722918919 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((867 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((565922361459461 / 9223372036854775808 : ℚ) : ℝ) ≤ ((35843653227 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_868 : ((998849462182665 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((217 / 2 : ℚ) : ℝ) ∧
    heightZ ((217 / 2 : ℚ) : ℝ) ≤ ((249712365545667 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((998849462182665 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((217 / 2 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-135 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((217 / 2 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-135 / 16 : ℚ) : ℝ) ≤ ((249712365545667 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_868 : ((27915065197 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((217 / 2 : ℚ) : ℝ) ∧
    logKernel ((217 / 2 : ℚ) : ℝ) ≤ ((13957532601 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_868
  constructor
  · exact (show ((27915065197 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((998849462182665 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((217 / 2 : ℚ) : ℝ)) hh).trans
      (show zKernel ((249712365545667 / 4611686018427387904 : ℚ) : ℝ) ≤ ((13957532601 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_869 : ((881481556524491 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((869 / 8 : ℚ) : ℝ) ∧
    heightZ ((869 / 8 : ℚ) : ℝ) ≤ ((440740778262247 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((881481556524491 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((869 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-137 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((869 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-137 / 16 : ℚ) : ℝ) ≤ ((440740778262247 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_869 : ((10870137317 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((869 / 8 : ℚ) : ℝ) ∧
    logKernel ((869 / 8 : ℚ) : ℝ) ≤ ((21740274639 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_869
  constructor
  · exact (show ((10870137317 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((881481556524491 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((869 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((440740778262247 / 9223372036854775808 : ℚ) : ℝ) ≤ ((21740274639 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_870 : ((777904743318311 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((435 / 4 : ℚ) : ℝ) ∧
    heightZ ((435 / 4 : ℚ) : ℝ) ≤ ((388952371659157 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((777904743318311 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((435 / 4 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-139 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((435 / 4 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-139 / 16 : ℚ) : ℝ) ≤ ((388952371659157 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_870 : ((16931342909 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((435 / 4 : ℚ) : ℝ) ∧
    logKernel ((435 / 4 : ℚ) : ℝ) ≤ ((8465671457 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_870
  constructor
  · exact (show ((16931342909 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((777904743318311 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((435 / 4 : ℚ) : ℝ)) hh).trans
      (show zKernel ((388952371659157 / 9223372036854775808 : ℚ) : ℝ) ≤ ((8465671457 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_871 : ((343249263242137 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((871 / 8 : ℚ) : ℝ) ∧
    heightZ ((871 / 8 : ℚ) : ℝ) ≤ ((686498526484277 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((343249263242137 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((871 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-141 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((871 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-141 / 16 : ℚ) : ℝ) ≤ ((686498526484277 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_871 : ((13186143115 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((871 / 8 : ℚ) : ℝ) ∧
    logKernel ((871 / 8 : ℚ) : ℝ) ≤ ((824133945 / 4503599627370496 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_871
  constructor
  · exact (show ((13186143115 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((343249263242137 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((871 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((686498526484277 / 18446744073709551616 : ℚ) : ℝ) ≤ ((824133945 / 4503599627370496 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_872 : ((605832823251261 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((109 / 1 : ℚ) : ℝ) ∧
    heightZ ((109 / 1 : ℚ) : ℝ) ≤ ((9466137863301 / 288230376151711744 : ℚ) : ℝ) := by
  have h : ((605832823251261 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((109 / 1 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-143 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((109 / 1 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-143 / 16 : ℚ) : ℝ) ≤ ((9466137863301 / 288230376151711744 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_872 : ((10269378583 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((109 / 1 : ℚ) : ℝ) ∧
    logKernel ((109 / 1 : ℚ) : ℝ) ≤ ((2567344647 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_872
  constructor
  · exact (show ((10269378583 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((605832823251261 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((109 / 1 : ℚ) : ℝ)) hh).trans
      (show zKernel ((9466137863301 / 288230376151711744 : ℚ) : ℝ) ≤ ((2567344647 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_873 : ((267322795001659 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((873 / 8 : ℚ) : ℝ) ∧
    heightZ ((873 / 8 : ℚ) : ℝ) ≤ ((534645590003321 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((267322795001659 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((873 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-145 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((873 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-145 / 16 : ℚ) : ℝ) ≤ ((534645590003321 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_873 : ((3998900041 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((873 / 8 : ℚ) : ℝ) ∧
    logKernel ((873 / 8 : ℚ) : ℝ) ≤ ((7997800087 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_873
  constructor
  · exact (show ((3998900041 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((267322795001659 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((873 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((534645590003321 / 18446744073709551616 : ℚ) : ℝ) ≤ ((7997800087 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_874 : ((471823077158441 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((437 / 4 : ℚ) : ℝ) ∧
    heightZ ((437 / 4 : ℚ) : ℝ) ≤ ((117955769289611 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((471823077158441 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((437 / 4 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-147 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((437 / 4 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-147 / 16 : ℚ) : ℝ) ≤ ((117955769289611 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_874 : ((3114346483 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((437 / 4 : ℚ) : ℝ) ∧
    logKernel ((437 / 4 : ℚ) : ℝ) ≤ ((6228692971 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_874
  constructor
  · exact (show ((3114346483 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((471823077158441 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((437 / 4 : ℚ) : ℝ)) hh).trans
      (show zKernel ((117955769289611 / 4611686018427387904 : ℚ) : ℝ) ≤ ((6228692971 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_875 : ((416382404160257 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((875 / 8 : ℚ) : ℝ) ∧
    heightZ ((875 / 8 : ℚ) : ℝ) ≤ ((104095601040065 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((416382404160257 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((875 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-149 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((875 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-149 / 16 : ℚ) : ℝ) ≤ ((104095601040065 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_875 : ((4850910959 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((875 / 8 : ℚ) : ℝ) ∧
    logKernel ((875 / 8 : ℚ) : ℝ) ≤ ((1212727741 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_875
  constructor
  · exact (show ((4850910959 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((416382404160257 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((875 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((104095601040065 / 4611686018427387904 : ℚ) : ℝ) ≤ ((1212727741 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_876 : ((183728090981077 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((219 / 2 : ℚ) : ℝ) ∧
    heightZ ((219 / 2 : ℚ) : ℝ) ≤ ((367456181962157 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((183728090981077 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((219 / 2 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-151 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((219 / 2 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-151 / 16 : ℚ) : ℝ) ≤ ((367456181962157 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_876 : ((3777893253 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((219 / 2 : ℚ) : ℝ) ∧
    logKernel ((219 / 2 : ℚ) : ℝ) ≤ ((1888946629 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_876
  constructor
  · exact (show ((3777893253 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((183728090981077 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((219 / 2 : ℚ) : ℝ)) hh).trans
      (show zKernel ((367456181962157 / 18446744073709551616 : ℚ) : ℝ) ≤ ((1888946629 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_877 : ((162139471208581 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((877 / 8 : ℚ) : ℝ) ∧
    heightZ ((877 / 8 : ℚ) : ℝ) ≤ ((324278942417165 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((162139471208581 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((877 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-153 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((877 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-153 / 16 : ℚ) : ℝ) ≤ ((324278942417165 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_877 : ((2942226223 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((877 / 8 : ℚ) : ℝ) ∧
    logKernel ((877 / 8 : ℚ) : ℝ) ≤ ((735556557 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_877
  constructor
  · exact (show ((2942226223 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((162139471208581 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((877 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((324278942417165 / 18446744073709551616 : ℚ) : ℝ) ≤ ((735556557 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_878 : ((143087581128277 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((439 / 4 : ℚ) : ℝ) ∧
    heightZ ((439 / 4 : ℚ) : ℝ) ≤ ((286175162256557 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((143087581128277 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((439 / 4 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-155 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((439 / 4 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-155 / 16 : ℚ) : ℝ) ≤ ((286175162256557 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_878 : ((1145704043 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((439 / 4 : ℚ) : ℝ) ∧
    logKernel ((439 / 4 : ℚ) : ℝ) ≤ ((2291408091 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_878
  constructor
  · exact (show ((1145704043 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((143087581128277 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((439 / 4 : ℚ) : ℝ)) hh).trans
      (show zKernel ((286175162256557 / 18446744073709551616 : ℚ) : ℝ) ≤ ((2291408091 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_879 : ((63137173572013 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((879 / 8 : ℚ) : ℝ) ∧
    heightZ ((879 / 8 : ℚ) : ℝ) ≤ ((252548694288055 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((63137173572013 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((879 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-157 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((879 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-157 / 16 : ℚ) : ℝ) ≤ ((252548694288055 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_879 : ((1784550411 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((879 / 8 : ℚ) : ℝ) ∧
    logKernel ((879 / 8 : ℚ) : ℝ) ≤ ((111534401 / 4503599627370496 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_879
  constructor
  · exact (show ((1784550411 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((63137173572013 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((879 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((252548694288055 / 18446744073709551616 : ℚ) : ℝ) ≤ ((111534401 / 4503599627370496 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_880 : ((111436720230495 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((110 / 1 : ℚ) : ℝ) ∧
    heightZ ((110 / 1 : ℚ) : ℝ) ≤ ((222873440460993 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((111436720230495 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((110 / 1 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-159 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((110 / 1 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-159 / 16 : ℚ) : ℝ) ≤ ((222873440460993 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_880 : ((1389809257 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((110 / 1 : ℚ) : ℝ) ∧
    logKernel ((110 / 1 : ℚ) : ℝ) ≤ ((694904631 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_880
  constructor
  · exact (show ((1389809257 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((111436720230495 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((110 / 1 : ℚ) : ℝ)) hh).trans
      (show zKernel ((222873440460993 / 18446744073709551616 : ℚ) : ℝ) ≤ ((694904631 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_881 : ((49171280218799 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((881 / 8 : ℚ) : ℝ) ∧
    heightZ ((881 / 8 : ℚ) : ℝ) ≤ ((196685120875199 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((49171280218799 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((881 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-161 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((881 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-161 / 16 : ℚ) : ℝ) ≤ ((196685120875199 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_881 : ((1082384537 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((881 / 8 : ℚ) : ℝ) ∧
    logKernel ((881 / 8 : ℚ) : ℝ) ≤ ((541192271 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_881
  constructor
  · exact (show ((1082384537 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((49171280218799 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((881 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((196685120875199 / 18446744073709551616 : ℚ) : ℝ) ≤ ((541192271 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_882 : ((173574009956837 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((441 / 4 : ℚ) : ℝ) ∧
    heightZ ((441 / 4 : ℚ) : ℝ) ≤ ((21696751244605 / 2305843009213693952 : ℚ) : ℝ) := by
  have h : ((173574009956837 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((441 / 4 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-163 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((441 / 4 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-163 / 16 : ℚ) : ℝ) ≤ ((21696751244605 / 2305843009213693952 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_882 : ((842961925 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((441 / 4 : ℚ) : ℝ) ∧
    logKernel ((441 / 4 : ℚ) : ℝ) ≤ ((421480965 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_882
  constructor
  · exact (show ((842961925 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((173574009956837 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((441 / 4 : ℚ) : ℝ)) hh).trans
      (show zKernel ((21696751244605 / 2305843009213693952 : ℚ) : ℝ) ≤ ((421480965 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_883 : ((2393414471189 / 288230376151711744 : ℚ) : ℝ) ≤ heightZ ((883 / 8 : ℚ) : ℝ) ∧
    heightZ ((883 / 8 : ℚ) : ℝ) ≤ ((153178526156099 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((2393414471189 / 288230376151711744 : ℚ) : ℝ) ≤ Real.exp (-((883 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-165 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((883 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-165 / 16 : ℚ) : ℝ) ≤ ((153178526156099 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_883 : ((328249703 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((883 / 8 : ℚ) : ℝ) ∧
    logKernel ((883 / 8 : ℚ) : ℝ) ≤ ((656499411 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_883
  constructor
  · exact (show ((328249703 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((2393414471189 / 288230376151711744 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((883 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((153178526156099 / 18446744073709551616 : ℚ) : ℝ) ≤ ((656499411 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_884 : ((33794893718807 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((221 / 2 : ℚ) : ℝ) ∧
    heightZ ((221 / 2 : ℚ) : ℝ) ≤ ((135179574875231 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((33794893718807 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((221 / 2 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-167 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((221 / 2 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-167 / 16 : ℚ) : ℝ) ≤ ((135179574875231 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_884 : ((511282251 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((221 / 2 : ℚ) : ℝ) ∧
    logKernel ((221 / 2 : ℚ) : ℝ) ≤ ((31955141 / 4503599627370496 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_884
  constructor
  · exact (show ((511282251 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((33794893718807 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((221 / 2 : ℚ) : ℝ)) hh).trans
      (show zKernel ((135179574875231 / 18446744073709551616 : ℚ) : ℝ) ≤ ((31955141 / 4503599627370496 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_885 : ((119295556120091 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((885 / 8 : ℚ) : ℝ) ∧
    heightZ ((885 / 8 : ℚ) : ℝ) ≤ ((59647778060047 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((119295556120091 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((885 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-169 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((885 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-169 / 16 : ℚ) : ℝ) ≤ ((59647778060047 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_885 : ((398187017 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((885 / 8 : ℚ) : ℝ) ∧
    logKernel ((885 / 8 : ℚ) : ℝ) ≤ ((199093511 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_885
  constructor
  · exact (show ((398187017 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((119295556120091 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((885 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((59647778060047 / 9223372036854775808 : ℚ) : ℝ) ≤ ((199093511 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_886 : ((105277958768087 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((443 / 4 : ℚ) : ℝ) ∧
    heightZ ((443 / 4 : ℚ) : ℝ) ≤ ((52638979384045 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((105277958768087 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((443 / 4 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-171 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((443 / 4 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-171 / 16 : ℚ) : ℝ) ≤ ((52638979384045 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_886 : ((38763545 / 9007199254740992 : ℚ) : ℝ) ≤ logKernel ((443 / 4 : ℚ) : ℝ) ∧
    logKernel ((443 / 4 : ℚ) : ℝ) ≤ ((310108365 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_886
  constructor
  · exact (show ((38763545 / 9007199254740992 : ℚ) : ℝ) ≤ zKernel ((105277958768087 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((443 / 4 : ℚ) : ℝ)) hh).trans
      (show zKernel ((52638979384045 / 9223372036854775808 : ℚ) : ℝ) ≤ ((310108365 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_887 : ((92907472523265 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((887 / 8 : ℚ) : ℝ) ∧
    heightZ ((887 / 8 : ℚ) : ℝ) ≤ ((23226868130817 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((92907472523265 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((887 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-173 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((887 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-173 / 16 : ℚ) : ℝ) ≤ ((23226868130817 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_887 : ((241512633 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((887 / 8 : ℚ) : ℝ) ∧
    logKernel ((887 / 8 : ℚ) : ℝ) ≤ ((120756319 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_887
  constructor
  · exact (show ((241512633 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((92907472523265 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((887 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((23226868130817 / 4611686018427387904 : ℚ) : ℝ) ≤ ((120756319 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_888 : ((81990556728745 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((111 / 1 : ℚ) : ℝ) ∧
    heightZ ((111 / 1 : ℚ) : ℝ) ≤ ((20497639182187 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((81990556728745 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((111 / 1 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-175 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((111 / 1 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-175 / 16 : ℚ) : ℝ) ≤ ((20497639182187 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_888 : ((188090227 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((111 / 1 : ℚ) : ℝ) ∧
    logKernel ((111 / 1 : ℚ) : ℝ) ≤ ((23511279 / 9007199254740992 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_888
  constructor
  · exact (show ((188090227 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((81990556728745 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((111 / 1 : ℚ) : ℝ)) hh).trans
      (show zKernel ((20497639182187 / 4611686018427387904 : ℚ) : ℝ) ≤ ((23511279 / 9007199254740992 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_889 : ((282642235759 / 72057594037927936 : ℚ) : ℝ) ≤ heightZ ((889 / 8 : ℚ) : ℝ) ∧
    heightZ ((889 / 8 : ℚ) : ℝ) ≤ ((72356412354307 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((282642235759 / 72057594037927936 : ℚ) : ℝ) ≤ Real.exp (-((889 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-177 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((889 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-177 / 16 : ℚ) : ℝ) ≤ ((72356412354307 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_889 : ((9155301 / 4503599627370496 : ℚ) : ℝ) ≤ logKernel ((889 / 8 : ℚ) : ℝ) ∧
    logKernel ((889 / 8 : ℚ) : ℝ) ≤ ((146484821 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_889
  constructor
  · exact (show ((9155301 / 4503599627370496 : ℚ) : ℝ) ≤ zKernel ((282642235759 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((889 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((72356412354307 / 18446744073709551616 : ℚ) : ℝ) ≤ ((146484821 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_890 : ((63854309784807 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((445 / 4 : ℚ) : ℝ) ∧
    heightZ ((445 / 4 : ℚ) : ℝ) ≤ ((31927154892405 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((63854309784807 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((445 / 4 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-179 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((445 / 4 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-179 / 16 : ℚ) : ℝ) ≤ ((31927154892405 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_890 : ((114082489 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((445 / 4 : ℚ) : ℝ) ∧
    logKernel ((445 / 4 : ℚ) : ℝ) ≤ ((57041247 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_890
  constructor
  · exact (show ((114082489 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((63854309784807 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((445 / 4 : ℚ) : ℝ)) hh).trans
      (show zKernel ((31927154892405 / 9223372036854775808 : ℚ) : ℝ) ≤ ((57041247 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

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

theorem log_height_bounds_64 : ((168524368305079023 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((215 / 2 : ℚ) : ℝ) ∧
    Real.log ((215 / 2 : ℚ) : ℝ) ≤ ((337048736610158049 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((168524368305079023 / 36028797018963968 : ℚ) : ℝ) ≤ ((215 / 2 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((215 / 2 : ℚ) : ℝ) ≤ Real.exp ((337048736610158049 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_64 : heightPower (64 : Fin 125) ≤ ((2301759045870727 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_64
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_64 : heightFactor (64 : Fin 125) ≤ ((80761584466507 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_64
  obtain ⟨hpl, hph⟩ := kernel_bounds_859
  obtain ⟨hcl, hch⟩ := kernel_bounds_860
  obtain ⟨hzl, hzh⟩ := height_z_bounds_860
  have h : (((46225 / 2 : ℚ) : ℝ) * (logKernel ((859 / 8 : ℚ) : ℝ) - logKernel ((215 / 2 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((215 / 2 : ℚ) : ℝ) + Real.log ((215 / 2 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((80761584466507 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_65 : ((168566237917018291 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((861 / 8 : ℚ) : ℝ) ∧
    Real.log ((861 / 8 : ℚ) : ℝ) ≤ ((337132475834036585 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((168566237917018291 / 36028797018963968 : ℚ) : ℝ) ≤ ((861 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((861 / 8 : ℚ) : ℝ) ≤ Real.exp ((337132475834036585 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_65 : heightPower (65 : Fin 125) ≤ ((2337270524302835 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_65
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_65 : heightFactor (65 : Fin 125) ≤ ((65751315891499 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_65
  obtain ⟨hpl, hph⟩ := kernel_bounds_860
  obtain ⟨hcl, hch⟩ := kernel_bounds_861
  obtain ⟨hzl, hzh⟩ := height_z_bounds_861
  have h : (((741321 / 32 : ℚ) : ℝ) * (logKernel ((215 / 2 : ℚ) : ℝ) - logKernel ((861 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((861 / 8 : ℚ) : ℝ) + Real.log ((861 / 8 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((65751315891499 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_66 : ((337216117856240487 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((431 / 4 : ℚ) : ℝ) ∧
    Real.log ((431 / 4 : ℚ) : ℝ) ≤ ((168608058928120245 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((337216117856240487 / 72057594037927936 : ℚ) : ℝ) ≤ ((431 / 4 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((431 / 4 : ℚ) : ℝ) ≤ Real.exp ((168608058928120245 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_66 : heightPower (66 : Fin 125) ≤ ((2372781623040901 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_66
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_66 : heightFactor (66 : Fin 125) ≤ ((26765336300837 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_66
  obtain ⟨hpl, hph⟩ := kernel_bounds_861
  obtain ⟨hcl, hch⟩ := kernel_bounds_862
  obtain ⟨hzl, hzh⟩ := height_z_bounds_862
  have h : (((185761 / 8 : ℚ) : ℝ) * (logKernel ((861 / 8 : ℚ) : ℝ) - logKernel ((431 / 4 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((431 / 4 : ℚ) : ℝ) + Real.log ((431 / 4 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((26765336300837 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_67 : ((10540614465692657 / 2251799813685248 : ℚ) : ℝ) ≤ Real.log ((863 / 8 : ℚ) : ℝ) ∧
    Real.log ((863 / 8 : ℚ) : ℝ) ≤ ((337299662902165027 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((10540614465692657 / 2251799813685248 : ℚ) : ℝ) ≤ ((863 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((863 / 8 : ℚ) : ℝ) ≤ Real.exp ((337299662902165027 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_67 : heightPower (67 : Fin 125) ≤ ((18814783929417 / 2199023255552 : ℚ) : ℝ) := by
  have hh := log_height_bounds_67
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_67 : heightFactor (67 : Fin 125) ≤ ((43581240531479 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_67
  obtain ⟨hpl, hph⟩ := kernel_bounds_862
  obtain ⟨hcl, hch⟩ := kernel_bounds_863
  obtain ⟨hzl, hzh⟩ := height_z_bounds_863
  have h : (((744769 / 32 : ℚ) : ℝ) * (logKernel ((431 / 4 : ℚ) : ℝ) - logKernel ((863 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((863 / 8 : ℚ) : ℝ) + Real.log ((863 / 8 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((43581240531479 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_68 : ((168691555598211191 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((108 / 1 : ℚ) : ℝ) ∧
    Real.log ((108 / 1 : ℚ) : ℝ) ≤ ((337383111196422385 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((168691555598211191 / 36028797018963968 : ℚ) : ℝ) ≤ ((108 / 1 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((108 / 1 : ℚ) : ℝ) ≤ Real.exp ((337383111196422385 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_68 : heightPower (68 : Fin 125) ≤ ((1221901342476825 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_68
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_68 : heightFactor (68 : Fin 125) ≤ ((8870234976439 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_68
  obtain ⟨hpl, hph⟩ := kernel_bounds_863
  obtain ⟨hcl, hch⟩ := kernel_bounds_864
  obtain ⟨hzl, hzh⟩ := height_z_bounds_864
  have h : (((23328 / 1 : ℚ) : ℝ) * (logKernel ((863 / 8 : ℚ) : ℝ) - logKernel ((108 / 1 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((108 / 1 : ℚ) : ℝ) + Real.log ((108 / 1 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((8870234976439 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_69 : ((337466462962845295 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((865 / 8 : ℚ) : ℝ) ∧
    Real.log ((865 / 8 : ℚ) : ℝ) ≤ ((168733231481422649 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((337466462962845295 / 72057594037927936 : ℚ) : ℝ) ≤ ((865 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((865 / 8 : ℚ) : ℝ) ≤ Real.exp ((168733231481422649 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_69 : heightPower (69 : Fin 125) ≤ ((309914081235009 / 35184372088832 : ℚ) : ℝ) := by
  have hh := log_height_bounds_69
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_69 : heightFactor (69 : Fin 125) ≤ ((28886125036209 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_69
  obtain ⟨hpl, hph⟩ := kernel_bounds_864
  obtain ⟨hcl, hch⟩ := kernel_bounds_865
  obtain ⟨hzl, hzh⟩ := height_z_bounds_865
  have h : (((748225 / 32 : ℚ) : ℝ) * (logKernel ((108 / 1 : ℚ) : ℝ) - logKernel ((865 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((865 / 8 : ℚ) : ℝ) + Real.log ((865 / 8 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((28886125036209 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_70 : ((42193714803061331 / 9007199254740992 : ℚ) : ℝ) ≤ Real.log ((433 / 4 : ℚ) : ℝ) ∧
    Real.log ((433 / 4 : ℚ) : ℝ) ≤ ((337549718424490651 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((42193714803061331 / 9007199254740992 : ℚ) : ℝ) ≤ ((433 / 4 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((433 / 4 : ℚ) : ℝ) ≤ Real.exp ((337549718424490651 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_70 : heightPower (70 : Fin 125) ≤ ((628705559653989 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_70
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_70 : heightFactor (70 : Fin 125) ≤ ((5879252501601 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_70
  obtain ⟨hpl, hph⟩ := kernel_bounds_865
  obtain ⟨hcl, hch⟩ := kernel_bounds_866
  obtain ⟨hzl, hzh⟩ := height_z_bounds_866
  have h : (((187489 / 8 : ℚ) : ℝ) * (logKernel ((865 / 8 : ℚ) : ℝ) - logKernel ((433 / 4 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((433 / 4 : ℚ) : ℝ) + Real.log ((433 / 4 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((5879252501601 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_71 : ((337632877803643055 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((867 / 8 : ℚ) : ℝ) ∧
    Real.log ((867 / 8 : ℚ) : ℝ) ≤ ((168816438901821529 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((337632877803643055 / 72057594037927936 : ℚ) : ℝ) ≤ ((867 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((867 / 8 : ℚ) : ℝ) ≤ Real.exp ((168816438901821529 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_71 : heightPower (71 : Fin 125) ≤ ((1275165726014801 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_71
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_71 : heightFactor (71 : Fin 125) ≤ ((19145802328831 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_71
  obtain ⟨hpl, hph⟩ := kernel_bounds_866
  obtain ⟨hcl, hch⟩ := kernel_bounds_867
  obtain ⟨hzl, hzh⟩ := height_z_bounds_867
  have h : (((751689 / 32 : ℚ) : ℝ) * (logKernel ((433 / 4 : ℚ) : ℝ) - logKernel ((867 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((867 / 8 : ℚ) : ℝ) + Real.log ((867 / 8 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((19145802328831 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_72 : ((42214492665227303 / 9007199254740992 : ℚ) : ℝ) ≤ Real.log ((217 / 2 : ℚ) : ℝ) ∧
    Real.log ((217 / 2 : ℚ) : ℝ) ≤ ((337715941321818427 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((42214492665227303 / 9007199254740992 : ℚ) : ℝ) ≤ ((217 / 2 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((217 / 2 : ℚ) : ℝ) ≤ Real.exp ((337715941321818427 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_72 : heightPower (72 : Fin 125) ≤ ((2585840290986307 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_72
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_72 : heightFactor (72 : Fin 125) ≤ ((15587041452805 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_72
  obtain ⟨hpl, hph⟩ := kernel_bounds_867
  obtain ⟨hcl, hch⟩ := kernel_bounds_868
  obtain ⟨hzl, hzh⟩ := height_z_bounds_868
  have h : (((47089 / 2 : ℚ) : ℝ) * (logKernel ((867 / 8 : ℚ) : ℝ) - logKernel ((217 / 2 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((217 / 2 : ℚ) : ℝ) + Real.log ((217 / 2 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((15587041452805 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_73 : ((42224863649970937 / 9007199254740992 : ℚ) : ℝ) ≤ Real.log ((869 / 8 : ℚ) : ℝ) ∧
    Real.log ((869 / 8 : ℚ) : ℝ) ≤ ((337798909199767499 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((42224863649970937 / 9007199254740992 : ℚ) : ℝ) ≤ ((869 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((869 / 8 : ℚ) : ℝ) ≤ Real.exp ((337798909199767499 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_73 : heightPower (73 : Fin 125) ≤ ((2621348756348377 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_73
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_73 : heightFactor (73 : Fin 125) ≤ ((6344866236093 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_73
  obtain ⟨hpl, hph⟩ := kernel_bounds_868
  obtain ⟨hcl, hch⟩ := kernel_bounds_869
  obtain ⟨hzl, hzh⟩ := height_z_bounds_869
  have h : (((755161 / 32 : ℚ) : ℝ) * (logKernel ((217 / 2 : ℚ) : ℝ) - logKernel ((869 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((869 / 8 : ℚ) : ℝ) + Real.log ((869 / 8 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((6344866236093 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_74 : ((337881781657479363 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((435 / 4 : ℚ) : ℝ) ∧
    Real.log ((435 / 4 : ℚ) : ℝ) ≤ ((168940890828739683 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((337881781657479363 / 72057594037927936 : ℚ) : ℝ) ≤ ((435 / 4 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((435 / 4 : ℚ) : ℝ) ≤ Real.exp ((168940890828739683 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_74 : heightPower (74 : Fin 125) ≤ ((1328428424487573 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_74
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_74 : heightFactor (74 : Fin 125) ≤ ((10330941488299 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_74
  obtain ⟨hpl, hph⟩ := kernel_bounds_869
  obtain ⟨hcl, hch⟩ := kernel_bounds_870
  obtain ⟨hzl, hzh⟩ := height_z_bounds_870
  have h : (((189225 / 8 : ℚ) : ℝ) * (logKernel ((869 / 8 : ℚ) : ℝ) - logKernel ((435 / 4 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((435 / 4 : ℚ) : ℝ) + Real.log ((435 / 4 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((10330941488299 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_75 : ((337964558914184969 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((871 / 8 : ℚ) : ℝ) ∧
    Real.log ((871 / 8 : ℚ) : ℝ) ≤ ((84491139728546243 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((337964558914184969 / 72057594037927936 : ℚ) : ℝ) ≤ ((871 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((871 / 8 : ℚ) : ℝ) ≤ Real.exp ((84491139728546243 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_75 : heightPower (75 : Fin 125) ≤ ((2692364569722985 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_75
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_75 : heightFactor (75 : Fin 125) ≤ ((4205290525701 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_75
  obtain ⟨hpl, hph⟩ := kernel_bounds_870
  obtain ⟨hcl, hch⟩ := kernel_bounds_871
  obtain ⟨hzl, hzh⟩ := height_z_bounds_871
  have h : (((758641 / 32 : ℚ) : ℝ) * (logKernel ((435 / 4 : ℚ) : ℝ) - logKernel ((871 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((871 / 8 : ℚ) : ℝ) + Real.log ((871 / 8 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((4205290525701 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_76 : ((21127952574272537 / 4503599627370496 : ℚ) : ℝ) ≤ Real.log ((109 / 1 : ℚ) : ℝ) ∧
    Real.log ((109 / 1 : ℚ) : ℝ) ≤ ((338047241188360595 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((21127952574272537 / 4503599627370496 : ℚ) : ℝ) ≤ ((109 / 1 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((109 / 1 : ℚ) : ℝ) ≤ Real.exp ((338047241188360595 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_76 : heightPower (76 : Fin 125) ≤ ((2727871919445315 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_76
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_76 : heightFactor (76 : Fin 125) ≤ ((3423582279995 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_76
  obtain ⟨hpl, hph⟩ := kernel_bounds_871
  obtain ⟨hcl, hch⟩ := kernel_bounds_872
  obtain ⟨hzl, hzh⟩ := height_z_bounds_872
  have h : (((23762 / 1 : ℚ) : ℝ) * (logKernel ((871 / 8 : ℚ) : ℝ) - logKernel ((109 / 1 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((109 / 1 : ℚ) : ℝ) + Real.log ((109 / 1 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((3423582279995 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_77 : ((338129828697731301 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((873 / 8 : ℚ) : ℝ) ∧
    Real.log ((873 / 8 : ℚ) : ℝ) ≤ ((42266228587216413 / 9007199254740992 : ℚ) : ℝ) := by
  have hl : Real.exp ((338129828697731301 / 72057594037927936 : ℚ) : ℝ) ≤ ((873 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((873 / 8 : ℚ) : ℝ) ≤ Real.exp ((42266228587216413 / 9007199254740992 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_77 : heightPower (77 : Fin 125) ≤ ((1381689449496313 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_77
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_77 : heightFactor (77 : Fin 125) ≤ ((2787174789801 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_77
  obtain ⟨hpl, hph⟩ := kernel_bounds_872
  obtain ⟨hcl, hch⟩ := kernel_bounds_873
  obtain ⟨hzl, hzh⟩ := height_z_bounds_873
  have h : (((762129 / 32 : ℚ) : ℝ) * (logKernel ((109 / 1 : ℚ) : ℝ) - logKernel ((873 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((873 / 8 : ℚ) : ℝ) + Real.log ((873 / 8 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((2787174789801 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_78 : ((338212321659274395 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((437 / 4 : ℚ) : ℝ) ∧
    Real.log ((437 / 4 : ℚ) : ℝ) ≤ ((169106160829637199 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((338212321659274395 / 72057594037927936 : ℚ) : ℝ) ≤ ((437 / 4 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((437 / 4 : ℚ) : ℝ) ≤ Real.exp ((169106160829637199 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_78 : heightPower (78 : Fin 125) ≤ ((1399442754606243 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_78
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_78 : heightFactor (78 : Fin 125) ≤ ((4538123492923 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_78
  obtain ⟨hpl, hph⟩ := kernel_bounds_873
  obtain ⟨hcl, hch⟩ := kernel_bounds_874
  obtain ⟨hzl, hzh⟩ := height_z_bounds_874
  have h : (((190969 / 8 : ℚ) : ℝ) * (logKernel ((873 / 8 : ℚ) : ℝ) - logKernel ((437 / 4 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((437 / 4 : ℚ) : ℝ) + Real.log ((437 / 4 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((4538123492923 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_79 : ((338294720289222827 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((875 / 8 : ℚ) : ℝ) ∧
    Real.log ((875 / 8 : ℚ) : ℝ) ≤ ((169147360144611415 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((338294720289222827 / 72057594037927936 : ℚ) : ℝ) ≤ ((875 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((875 / 8 : ℚ) : ℝ) ≤ Real.exp ((169147360144611415 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_79 : heightPower (79 : Fin 125) ≤ ((1417195875474777 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_79
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_79 : heightFactor (79 : Fin 125) ≤ ((461814016077 / 35184372088832 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_79
  obtain ⟨hpl, hph⟩ := kernel_bounds_874
  obtain ⟨hcl, hch⟩ := kernel_bounds_875
  obtain ⟨hzl, hzh⟩ := height_z_bounds_875
  have h : (((765625 / 32 : ℚ) : ℝ) * (logKernel ((437 / 4 : ℚ) : ℝ) - logKernel ((875 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((875 / 8 : ℚ) : ℝ) + Real.log ((875 / 8 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((461814016077 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_80 : ((338377024803068603 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((219 / 2 : ℚ) : ℝ) ∧
    Real.log ((219 / 2 : ℚ) : ℝ) ≤ ((169188512401534303 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((338377024803068603 / 72057594037927936 : ℚ) : ℝ) ≤ ((219 / 2 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((219 / 2 : ℚ) : ℝ) ≤ Real.exp ((169188512401534303 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_80 : heightPower (80 : Fin 125) ≤ ((717474406261399 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_80
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_80 : heightFactor (80 : Fin 125) ≤ ((3007714192007 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_80
  obtain ⟨hpl, hph⟩ := kernel_bounds_875
  obtain ⟨hcl, hch⟩ := kernel_bounds_876
  obtain ⟨hzl, hzh⟩ := height_z_bounds_876
  have h : (((47961 / 2 : ℚ) : ℝ) * (logKernel ((875 / 8 : ℚ) : ℝ) - logKernel ((219 / 2 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((219 / 2 : ℚ) : ℝ) + Real.log ((219 / 2 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((3007714192007 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_81 : ((338459235415566163 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((877 / 8 : ℚ) : ℝ) ∧
    Real.log ((877 / 8 : ℚ) : ℝ) ≤ ((169229617707783083 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((338459235415566163 / 72057594037927936 : ℚ) : ℝ) ≤ ((877 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((877 / 8 : ℚ) : ℝ) ≤ Real.exp ((169229617707783083 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_81 : heightPower (81 : Fin 125) ≤ ((2905403132339497 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_81
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_81 : heightFactor (81 : Fin 125) ≤ ((2448582376477 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_81
  obtain ⟨hpl, hph⟩ := kernel_bounds_876
  obtain ⟨hcl, hch⟩ := kernel_bounds_877
  obtain ⟨hzl, hzh⟩ := height_z_bounds_877
  have h : (((769129 / 32 : ℚ) : ℝ) * (logKernel ((219 / 2 : ℚ) : ℝ) - logKernel ((877 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((877 / 8 : ℚ) : ℝ) + Real.log ((877 / 8 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((2448582376477 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_82 : ((1322427157580999 / 281474976710656 : ℚ) : ℝ) ≤ Real.log ((439 / 4 : ℚ) : ℝ) ∧
    Real.log ((439 / 4 : ℚ) : ℝ) ≤ ((338541352340735747 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((1322427157580999 / 281474976710656 : ℚ) : ℝ) ≤ ((439 / 4 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((439 / 4 : ℚ) : ℝ) ≤ Real.exp ((338541352340735747 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_82 : heightPower (82 : Fin 125) ≤ ((2940908273667273 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_82
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_82 : heightFactor (82 : Fin 125) ≤ ((1993386735487 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_82
  obtain ⟨hpl, hph⟩ := kernel_bounds_877
  obtain ⟨hcl, hch⟩ := kernel_bounds_878
  obtain ⟨hzl, hzh⟩ := height_z_bounds_878
  have h : (((192721 / 8 : ℚ) : ℝ) * (logKernel ((877 / 8 : ℚ) : ℝ) - logKernel ((439 / 4 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((439 / 4 : ℚ) : ℝ) + Real.log ((439 / 4 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((1993386735487 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_83 : ((338623375791866721 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((879 / 8 : ℚ) : ℝ) ∧
    Real.log ((879 / 8 : ℚ) : ℝ) ≤ ((84655843947966681 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((338623375791866721 / 72057594037927936 : ℚ) : ℝ) ≤ ((879 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((879 / 8 : ℚ) : ℝ) ≤ Real.exp ((84655843947966681 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_83 : heightPower (83 : Fin 125) ≤ ((2976413049862085 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_83
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_83 : heightFactor (83 : Fin 125) ≤ ((1622807864977 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_83
  obtain ⟨hpl, hph⟩ := kernel_bounds_878
  obtain ⟨hcl, hch⟩ := kernel_bounds_879
  obtain ⟨hzl, hzh⟩ := height_z_bounds_879
  have h : (((772641 / 32 : ℚ) : ℝ) * (logKernel ((439 / 4 : ℚ) : ℝ) - logKernel ((879 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((879 / 8 : ℚ) : ℝ) + Real.log ((879 / 8 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((1622807864977 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_84 : ((169352652990760467 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((110 / 1 : ℚ) : ℝ) ∧
    Real.log ((110 / 1 : ℚ) : ℝ) ≤ ((338705305981520937 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((169352652990760467 / 36028797018963968 : ℚ) : ℝ) ≤ ((110 / 1 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((110 / 1 : ℚ) : ℝ) ≤ Real.exp ((338705305981520937 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_84 : heightPower (84 : Fin 125) ≤ ((1505958730877127 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_84
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_84 : heightFactor (84 : Fin 125) ≤ ((660558595821 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_84
  obtain ⟨hpl, hph⟩ := kernel_bounds_879
  obtain ⟨hcl, hch⟩ := kernel_bounds_880
  obtain ⟨hzl, hzh⟩ := height_z_bounds_880
  have h : (((24200 / 1 : ℚ) : ℝ) * (logKernel ((879 / 8 : ℚ) : ℝ) - logKernel ((110 / 1 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((110 / 1 : ℚ) : ℝ) + Real.log ((110 / 1 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((660558595821 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_85 : ((169393571560767995 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((881 / 8 : ℚ) : ℝ) ∧
    Real.log ((881 / 8 : ℚ) : ℝ) ≤ ((338787143121535993 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((169393571560767995 / 36028797018963968 : ℚ) : ℝ) ≤ ((881 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((881 / 8 : ℚ) : ℝ) ≤ Real.exp ((338787143121535993 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_85 : heightPower (85 : Fin 125) ≤ ((3047421510171269 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_85
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_85 : heightFactor (85 : Fin 125) ≤ ((268877399421 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_85
  obtain ⟨hpl, hph⟩ := kernel_bounds_880
  obtain ⟨hcl, hch⟩ := kernel_bounds_881
  obtain ⟨hzl, hzh⟩ := height_z_bounds_881
  have h : (((776161 / 32 : ℚ) : ℝ) * (logKernel ((110 / 1 : ℚ) : ℝ) - logKernel ((881 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((881 / 8 : ℚ) : ℝ) + Real.log ((881 / 8 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((268877399421 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_86 : ((338868887423028553 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((441 / 4 : ℚ) : ℝ) ∧
    Real.log ((441 / 4 : ℚ) : ℝ) ≤ ((84717221855757139 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((338868887423028553 / 72057594037927936 : ℚ) : ℝ) ≤ ((441 / 4 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((441 / 4 : ℚ) : ℝ) ≤ Real.exp ((84717221855757139 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_86 : heightPower (86 : Fin 125) ≤ ((3082925195937807 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_86
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_86 : heightFactor (86 : Fin 125) ≤ ((875560073341 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_86
  obtain ⟨hpl, hph⟩ := kernel_bounds_881
  obtain ⟨hcl, hch⟩ := kernel_bounds_882
  obtain ⟨hzl, hzh⟩ := height_z_bounds_882
  have h : (((194481 / 8 : ℚ) : ℝ) * (logKernel ((881 / 8 : ℚ) : ℝ) - logKernel ((441 / 4 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((441 / 4 : ℚ) : ℝ) + Real.log ((441 / 4 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((875560073341 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_87 : ((338950539096397607 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((883 / 8 : ℚ) : ℝ) ∧
    Real.log ((883 / 8 : ℚ) : ℝ) ≤ ((169475269548198805 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((338950539096397607 / 72057594037927936 : ℚ) : ℝ) ≤ ((883 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((883 / 8 : ℚ) : ℝ) ≤ Real.exp ((169475269548198805 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_87 : heightPower (87 : Fin 125) ≤ ((3118428519875737 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_87
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_87 : heightFactor (87 : Fin 125) ≤ ((178195337187 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_87
  obtain ⟨hpl, hph⟩ := kernel_bounds_882
  obtain ⟨hcl, hch⟩ := kernel_bounds_883
  obtain ⟨hzl, hzh⟩ := height_z_bounds_883
  have h : (((779689 / 32 : ℚ) : ℝ) * (logKernel ((441 / 4 : ℚ) : ℝ) - logKernel ((883 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((883 / 8 : ℚ) : ℝ) + Real.log ((883 / 8 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((178195337187 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_88 : ((339032098351327711 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((221 / 2 : ℚ) : ℝ) ∧
    Real.log ((221 / 2 : ℚ) : ℝ) ≤ ((169516049175663857 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((339032098351327711 / 72057594037927936 : ℚ) : ℝ) ≤ ((221 / 2 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((221 / 2 : ℚ) : ℝ) ≤ Real.exp ((169516049175663857 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_88 : heightPower (88 : Fin 125) ≤ ((3153931482804139 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_88
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_88 : heightFactor (88 : Fin 125) ≤ ((290131869813 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_88
  obtain ⟨hpl, hph⟩ := kernel_bounds_883
  obtain ⟨hcl, hch⟩ := kernel_bounds_884
  obtain ⟨hzl, hzh⟩ := height_z_bounds_884
  have h : (((48841 / 2 : ℚ) : ℝ) * (logKernel ((883 / 8 : ℚ) : ℝ) - logKernel ((221 / 2 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((221 / 2 : ℚ) : ℝ) + Real.log ((221 / 2 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((290131869813 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_89 : ((339113565396792223 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((885 / 8 : ℚ) : ℝ) ∧
    Real.log ((885 / 8 : ℚ) : ℝ) ≤ ((169556782698396113 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((339113565396792223 / 72057594037927936 : ℚ) : ℝ) ≤ ((885 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((885 / 8 : ℚ) : ℝ) ≤ Real.exp ((169556782698396113 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_89 : heightPower (89 : Fin 125) ≤ ((3189434085539317 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_89
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_89 : heightFactor (89 : Fin 125) ≤ ((472381928329 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_89
  obtain ⟨hpl, hph⟩ := kernel_bounds_884
  obtain ⟨hcl, hch⟩ := kernel_bounds_885
  obtain ⟨hzl, hzh⟩ := height_z_bounds_885
  have h : (((783225 / 32 : ℚ) : ℝ) * (logKernel ((221 / 2 : ℚ) : ℝ) - logKernel ((885 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((885 / 8 : ℚ) : ℝ) + Real.log ((885 / 8 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((472381928329 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_90 : ((339194940441056521 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((443 / 4 : ℚ) : ℝ) ∧
    Real.log ((443 / 4 : ℚ) : ℝ) ≤ ((84798735110264131 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((339194940441056521 / 72057594037927936 : ℚ) : ℝ) ≤ ((443 / 4 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((443 / 4 : ℚ) : ℝ) ≤ Real.exp ((84798735110264131 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_90 : heightPower (90 : Fin 125) ≤ ((3224936328894807 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_90
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_90 : heightFactor (90 : Fin 125) ≤ ((384556240945 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_90
  obtain ⟨hpl, hph⟩ := kernel_bounds_885
  obtain ⟨hcl, hch⟩ := kernel_bounds_886
  obtain ⟨hzl, hzh⟩ := height_z_bounds_886
  have h : (((196249 / 8 : ℚ) : ℝ) * (logKernel ((885 / 8 : ℚ) : ℝ) - logKernel ((443 / 4 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((443 / 4 : ℚ) : ℝ) + Real.log ((443 / 4 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((384556240945 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_91 : ((339276223691681189 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((887 / 8 : ℚ) : ℝ) ∧
    Real.log ((887 / 8 : ℚ) : ℝ) ≤ ((42409527961460149 / 9007199254740992 : ℚ) : ℝ) := by
  have hl : Real.exp ((339276223691681189 / 72057594037927936 : ℚ) : ℝ) ≤ ((887 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((887 / 8 : ℚ) : ℝ) ≤ Real.exp ((42409527961460149 / 9007199254740992 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_91 : heightPower (91 : Fin 125) ≤ ((3260438213681391 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_91
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_91 : heightFactor (91 : Fin 125) ≤ ((313058292737 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_91
  obtain ⟨hpl, hph⟩ := kernel_bounds_886
  obtain ⟨hcl, hch⟩ := kernel_bounds_887
  obtain ⟨hzl, hzh⟩ := height_z_bounds_887
  have h : (((786769 / 32 : ℚ) : ℝ) * (logKernel ((443 / 4 : ℚ) : ℝ) - logKernel ((887 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((887 / 8 : ℚ) : ℝ) + Real.log ((887 / 8 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((313058292737 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_92 : ((339357415355525199 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((111 / 1 : ℚ) : ℝ) ∧
    Real.log ((111 / 1 : ℚ) : ℝ) ≤ ((169678707677762601 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((339357415355525199 / 72057594037927936 : ℚ) : ℝ) ≤ ((111 / 1 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((111 / 1 : ℚ) : ℝ) ≤ Real.exp ((169678707677762601 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_92 : heightPower (92 : Fin 125) ≤ ((1647969870353557 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_92
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_92 : heightFactor (92 : Fin 125) ≤ ((254852756243 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_92
  obtain ⟨hpl, hph⟩ := kernel_bounds_887
  obtain ⟨hcl, hch⟩ := kernel_bounds_888
  obtain ⟨hzl, hzh⟩ := height_z_bounds_888
  have h : (((24642 / 1 : ℚ) : ℝ) * (logKernel ((887 / 8 : ℚ) : ℝ) - logKernel ((111 / 1 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((111 / 1 : ℚ) : ℝ) + Real.log ((111 / 1 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((254852756243 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_93 : ((84859628909687267 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((889 / 8 : ℚ) : ℝ) ∧
    Real.log ((889 / 8 : ℚ) : ℝ) ≤ ((339438515638749071 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((84859628909687267 / 18014398509481984 : ℚ) : ℝ) ≤ ((889 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((889 / 8 : ℚ) : ℝ) ≤ Real.exp ((339438515638749071 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_93 : heightPower (93 : Fin 125) ≤ ((3331440910777289 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_93
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_93 : heightFactor (93 : Fin 125) ≤ ((207468538705 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_93
  obtain ⟨hpl, hph⟩ := kernel_bounds_888
  obtain ⟨hcl, hch⟩ := kernel_bounds_889
  obtain ⟨hzl, hzh⟩ := height_z_bounds_889
  have h : (((790321 / 32 : ℚ) : ℝ) * (logKernel ((111 / 1 : ℚ) : ℝ) - logKernel ((889 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((889 / 8 : ℚ) : ℝ) + Real.log ((889 / 8 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((207468538705 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_94 : ((21219970296676125 / 4503599627370496 : ℚ) : ℝ) ≤ Real.log ((445 / 4 : ℚ) : ℝ) ∧
    Real.log ((445 / 4 : ℚ) : ℝ) ≤ ((339519524746818003 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((21219970296676125 / 4503599627370496 : ℚ) : ℝ) ≤ ((445 / 4 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((445 / 4 : ℚ) : ℝ) ≤ Real.exp ((339519524746818003 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_94 : heightPower (94 : Fin 125) ≤ ((3366941724694515 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_94
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_94 : heightFactor (94 : Fin 125) ≤ ((168893903075 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_94
  obtain ⟨hpl, hph⟩ := kernel_bounds_889
  obtain ⟨hcl, hch⟩ := kernel_bounds_890
  obtain ⟨hzl, hzh⟩ := height_z_bounds_890
  have h : (((198025 / 8 : ℚ) : ℝ) * (logKernel ((889 / 8 : ℚ) : ℝ) - logKernel ((445 / 4 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((445 / 4 : ℚ) : ℝ) + Real.log ((445 / 4 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((168893903075 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_95 : ((169800221442252503 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((891 / 8 : ℚ) : ℝ) ∧
    Real.log ((891 / 8 : ℚ) : ℝ) ≤ ((339600442884505009 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((169800221442252503 / 36028797018963968 : ℚ) : ℝ) ≤ ((891 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((891 / 8 : ℚ) : ℝ) ≤ Real.exp ((339600442884505009 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_95 : heightPower (95 : Fin 125) ≤ ((3402442183258687 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_95
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_95 : heightFactor (95 : Fin 125) ≤ ((68745541293 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_95
  obtain ⟨hpl, hph⟩ := kernel_bounds_890
  obtain ⟨hcl, hch⟩ := kernel_bounds_891
  obtain ⟨hzl, hzh⟩ := height_z_bounds_891
  have h : (((793881 / 32 : ℚ) : ℝ) * (logKernel ((445 / 4 : ℚ) : ℝ) - logKernel ((891 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((891 / 8 : ℚ) : ℝ) + Real.log ((891 / 8 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((68745541293 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

end LegendreK6.M3Far.Enclosures.Height002
