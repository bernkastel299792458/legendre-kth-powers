import LegendreK6.M2PilotDefinitions
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp

/-! Generated proposals: every bound is checked by Lean, not by trusting Arb. -/
namespace LegendreK6.M2Pilot.Enclosures.Height007
set_option maxRecDepth 100000
set_option maxHeartbeats 0

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

theorem height_z_bounds_2066 : ((265859247774733859 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1033 / 32 : ℚ) : ℝ) ∧
    heightZ ((1033 / 32 : ℚ) : ℝ) ≤ ((132929623887366931 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((265859247774733859 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1033 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-235 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1033 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-235 / 96 : ℚ) : ℝ) ≤ ((132929623887366931 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2066 : ((1977616648715385 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1033 / 32 : ℚ) : ℝ) ∧
    logKernel ((1033 / 32 : ℚ) : ℝ) ≤ ((988808324357695 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2066
  constructor
  · exact (show ((1977616648715385 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((265859247774733859 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1033 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((132929623887366931 / 9223372036854775808 : ℚ) : ℝ) ≤ ((988808324357695 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2067 : ((130868741089581769 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2067 / 64 : ℚ) : ℝ) ∧
    heightZ ((2067 / 64 : ℚ) : ℝ) ≤ ((261737482179163541 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((130868741089581769 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2067 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-473 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2067 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-473 / 192 : ℚ) : ℝ) ≤ ((261737482179163541 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2067 : ((239596472623585 / 9007199254740992 : ℚ) : ℝ) ≤ logKernel ((2067 / 64 : ℚ) : ℝ) ∧
    logKernel ((2067 / 64 : ℚ) : ℝ) ≤ ((1916771780988685 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2067
  constructor
  · exact (show ((239596472623585 / 9007199254740992 : ℚ) : ℝ) ≤ zKernel ((130868741089581769 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2067 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((261737482179163541 / 18446744073709551616 : ℚ) : ℝ) ≤ ((1916771780988685 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2068 : ((257679618636153081 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((517 / 16 : ℚ) : ℝ) ∧
    heightZ ((517 / 16 : ℚ) : ℝ) ≤ ((64419904659038271 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((257679618636153081 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((517 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-119 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((517 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-119 / 48 : ℚ) : ℝ) ≤ ((64419904659038271 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2068 : ((1857798913040641 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((517 / 16 : ℚ) : ℝ) ∧
    logKernel ((517 / 16 : ℚ) : ℝ) ≤ ((928899456520323 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2068
  constructor
  · exact (show ((1857798913040641 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((257679618636153081 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((517 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((64419904659038271 / 4611686018427387904 : ℚ) : ℝ) ≤ ((928899456520323 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2069 : ((31710583304525643 / 2305843009213693952 : ℚ) : ℝ) ≤ heightZ ((2069 / 64 : ℚ) : ℝ) ∧
    heightZ ((2069 / 64 : ℚ) : ℝ) ≤ ((253684666436205147 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((31710583304525643 / 2305843009213693952 : ℚ) : ℝ) ≤ Real.exp (-((2069 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-479 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2069 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-479 / 192 : ℚ) : ℝ) ≤ ((253684666436205147 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2069 : ((1800640449493017 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2069 / 64 : ℚ) : ℝ) ∧
    logKernel ((2069 / 64 : ℚ) : ℝ) ≤ ((900320224746511 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2069
  constructor
  · exact (show ((1800640449493017 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((31710583304525643 / 2305843009213693952 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2069 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((253684666436205147 / 18446744073709551616 : ℚ) : ℝ) ≤ ((900320224746511 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2070 : ((124875825114674741 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((1035 / 32 : ℚ) : ℝ) ∧
    heightZ ((1035 / 32 : ℚ) : ℝ) ≤ ((249751650229349485 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((124875825114674741 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((1035 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-241 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1035 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-241 / 96 : ℚ) : ℝ) ≤ ((249751650229349485 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2070 : ((1745240566991055 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1035 / 32 : ℚ) : ℝ) ∧
    logKernel ((1035 / 32 : ℚ) : ℝ) ≤ ((436310141747765 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2070
  constructor
  · exact (show ((1745240566991055 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((124875825114674741 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1035 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((249751650229349485 / 18446744073709551616 : ℚ) : ℝ) ≤ ((436310141747765 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2071 : ((61469902446753889 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((2071 / 64 : ℚ) : ℝ) ∧
    heightZ ((2071 / 64 : ℚ) : ℝ) ≤ ((245879609787015559 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((61469902446753889 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((2071 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-485 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2071 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-485 / 192 : ℚ) : ℝ) ≤ ((245879609787015559 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2071 : ((422886289921017 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((2071 / 64 : ℚ) : ℝ) ∧
    logKernel ((2071 / 64 : ℚ) : ℝ) ≤ ((1691545159684073 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2071
  constructor
  · exact (show ((422886289921017 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((61469902446753889 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2071 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((245879609787015559 / 18446744073709551616 : ℚ) : ℝ) ≤ ((1691545159684073 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2072 : ((7564612492737405 / 576460752303423488 : ℚ) : ℝ) ≤ heightZ ((259 / 8 : ℚ) : ℝ) ∧
    heightZ ((259 / 8 : ℚ) : ℝ) ≤ ((242067599767596963 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((7564612492737405 / 576460752303423488 : ℚ) : ℝ) ≤ Real.exp (-((259 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-61 / 24 : ℚ) : ℝ) ∧
      Real.exp (-((259 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-61 / 24 : ℚ) : ℝ) ≤ ((242067599767596963 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2072 : ((819750893191697 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((259 / 8 : ℚ) : ℝ) ∧
    logKernel ((259 / 8 : ℚ) : ℝ) ≤ ((1639501786383399 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2072
  constructor
  · exact (show ((819750893191697 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((7564612492737405 / 576460752303423488 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((259 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((242067599767596963 / 18446744073709551616 : ℚ) : ℝ) ≤ ((1639501786383399 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2073 : ((238314689485650435 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2073 / 64 : ℚ) : ℝ) ∧
    heightZ ((2073 / 64 : ℚ) : ℝ) ≤ ((119157344742825219 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((238314689485650435 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2073 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-491 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2073 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-491 / 192 : ℚ) : ℝ) ≤ ((119157344742825219 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2073 : ((1589059619346121 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2073 / 64 : ℚ) : ℝ) ∧
    logKernel ((2073 / 64 : ℚ) : ℝ) ≤ ((794529809673063 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2073
  constructor
  · exact (show ((1589059619346121 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((238314689485650435 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2073 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((119157344742825219 / 9223372036854775808 : ℚ) : ℝ) ≤ ((794529809673063 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2074 : ((234619962684673119 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1037 / 32 : ℚ) : ℝ) ∧
    heightZ ((1037 / 32 : ℚ) : ℝ) ≤ ((117309981342336561 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((234619962684673119 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1037 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-247 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1037 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-247 / 96 : ℚ) : ℝ) ≤ ((117309981342336561 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2074 : ((385042348658647 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((1037 / 32 : ℚ) : ℝ) ∧
    logKernel ((1037 / 32 : ℚ) : ℝ) ≤ ((1540169394634593 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2074
  constructor
  · exact (show ((385042348658647 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((234619962684673119 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1037 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((117309981342336561 / 9223372036854775808 : ℚ) : ℝ) ≤ ((1540169394634593 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2075 : ((3609101833021915 / 288230376151711744 : ℚ) : ℝ) ≤ heightZ ((2075 / 64 : ℚ) : ℝ) ∧
    heightZ ((2075 / 64 : ℚ) : ℝ) ≤ ((230982517313402563 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((3609101833021915 / 288230376151711744 : ℚ) : ℝ) ≤ Real.exp (-((2075 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-497 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2075 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-497 / 192 : ℚ) : ℝ) ≤ ((230982517313402563 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2075 : ((1492783364003155 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2075 / 64 : ℚ) : ℝ) ∧
    logKernel ((2075 / 64 : ℚ) : ℝ) ≤ ((186597920500395 / 9007199254740992 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2075
  constructor
  · exact (show ((1492783364003155 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((3609101833021915 / 288230376151711744 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2075 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((230982517313402563 / 18446744073709551616 : ℚ) : ℝ) ≤ ((186597920500395 / 9007199254740992 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2076 : ((14212591581599055 / 1152921504606846976 : ℚ) : ℝ) ≤ heightZ ((519 / 16 : ℚ) : ℝ) ∧
    heightZ ((519 / 16 : ℚ) : ℝ) ≤ ((227401465305584883 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((14212591581599055 / 1152921504606846976 : ℚ) : ℝ) ≤ Real.exp (-((519 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-125 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((519 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-125 / 48 : ℚ) : ℝ) ≤ ((227401465305584883 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2076 : ((1446855248265255 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((519 / 16 : ℚ) : ℝ) ∧
    logKernel ((519 / 16 : ℚ) : ℝ) ≤ ((361713812066315 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2076
  constructor
  · exact (show ((1446855248265255 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((14212591581599055 / 1152921504606846976 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((519 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((227401465305584883 / 18446744073709551616 : ℚ) : ℝ) ≤ ((361713812066315 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2077 : ((111937966181578655 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2077 / 64 : ℚ) : ℝ) ∧
    heightZ ((2077 / 64 : ℚ) : ℝ) ≤ ((223875932363157313 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((111937966181578655 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2077 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-503 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2077 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-503 / 192 : ℚ) : ℝ) ≤ ((223875932363157313 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2077 : ((1402340192095207 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2077 / 64 : ℚ) : ℝ) ∧
    logKernel ((2077 / 64 : ℚ) : ℝ) ≤ ((350585048023803 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2077
  constructor
  · exact (show ((1402340192095207 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((111937966181578655 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2077 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((223875932363157313 / 18446744073709551616 : ℚ) : ℝ) ≤ ((350585048023803 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2078 : ((220405057742792173 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1039 / 32 : ℚ) : ℝ) ∧
    heightZ ((1039 / 32 : ℚ) : ℝ) ≤ ((13775316108924511 / 1152921504606846976 : ℚ) : ℝ) := by
  have h : ((220405057742792173 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1039 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-253 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1039 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-253 / 96 : ℚ) : ℝ) ≤ ((13775316108924511 / 1152921504606846976 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2078 : ((1359194720220615 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1039 / 32 : ℚ) : ℝ) ∧
    logKernel ((1039 / 32 : ℚ) : ℝ) ≤ ((339798680055155 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2078
  constructor
  · exact (show ((1359194720220615 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((220405057742792173 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1039 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((13775316108924511 / 1152921504606846976 : ℚ) : ℝ) ≤ ((339798680055155 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2079 : ((216987994045750197 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2079 / 64 : ℚ) : ℝ) ∧
    heightZ ((2079 / 64 : ℚ) : ℝ) ≤ ((27123499255718775 / 2305843009213693952 : ℚ) : ℝ) := by
  have h : ((216987994045750197 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2079 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-509 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2079 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-509 / 192 : ℚ) : ℝ) ≤ ((27123499255718775 / 2305843009213693952 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2079 : ((1317376694962597 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2079 / 64 : ℚ) : ℝ) ∧
    logKernel ((2079 / 64 : ℚ) : ℝ) ≤ ((658688347481301 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2079
  constructor
  · exact (show ((1317376694962597 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((216987994045750197 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2079 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((27123499255718775 / 2305843009213693952 : ℚ) : ℝ) ≤ ((658688347481301 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2080 : ((213623907010991843 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((65 / 2 : ℚ) : ℝ) ∧
    heightZ ((65 / 2 : ℚ) : ℝ) ≤ ((106811953505495923 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((213623907010991843 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((65 / 2 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-8 / 3 : ℚ) : ℝ) ∧
      Real.exp (-((65 / 2 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-8 / 3 : ℚ) : ℝ) ≤ ((106811953505495923 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2080 : ((1276845275082353 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((65 / 2 : ℚ) : ℝ) ∧
    logKernel ((65 / 2 : ℚ) : ℝ) ≤ ((638422637541179 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2080
  constructor
  · exact (show ((1276845275082353 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((213623907010991843 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((65 / 2 : ℚ) : ℝ)) hh).trans
      (show zKernel ((106811953505495923 / 9223372036854775808 : ℚ) : ℝ) ≤ ((638422637541179 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2081 : ((105155987655748077 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2081 / 64 : ℚ) : ℝ) ∧
    heightZ ((2081 / 64 : ℚ) : ℝ) ≤ ((210311975311496157 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((105155987655748077 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2081 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-515 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2081 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-515 / 192 : ℚ) : ℝ) ≤ ((210311975311496157 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2081 : ((1237560875893907 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2081 / 64 : ℚ) : ℝ) ∧
    logKernel ((2081 / 64 : ℚ) : ℝ) ≤ ((154695109486739 / 9007199254740992 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2081
  constructor
  · exact (show ((1237560875893907 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((105155987655748077 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2081 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((210311975311496157 / 18446744073709551616 : ℚ) : ℝ) ≤ ((154695109486739 / 9007199254740992 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2082 : ((103525695176868691 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((1041 / 32 : ℚ) : ℝ) ∧
    heightZ ((1041 / 32 : ℚ) : ℝ) ≤ ((207051390353737385 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((103525695176868691 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((1041 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-259 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1041 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-259 / 96 : ℚ) : ℝ) ≤ ((207051390353737385 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2082 : ((1199485130604029 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1041 / 32 : ℚ) : ℝ) ∧
    logKernel ((1041 / 32 : ℚ) : ℝ) ≤ ((599742565302017 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2082
  constructor
  · exact (show ((1199485130604029 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((103525695176868691 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1041 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((207051390353737385 / 18446744073709551616 : ℚ) : ℝ) ≤ ((599742565302017 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2083 : ((25480169510033805 / 2305843009213693952 : ℚ) : ℝ) ≤ heightZ ((2083 / 64 : ℚ) : ℝ) ∧
    heightZ ((2083 / 64 : ℚ) : ℝ) ≤ ((203841356080270443 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((25480169510033805 / 2305843009213693952 : ℚ) : ℝ) ≤ Real.exp (-((2083 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-521 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2083 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-521 / 192 : ℚ) : ℝ) ≤ ((203841356080270443 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2083 : ((1162580852841623 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2083 / 64 : ℚ) : ℝ) ∧
    logKernel ((2083 / 64 : ℚ) : ℝ) ≤ ((290645213210407 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2083
  constructor
  · exact (show ((1162580852841623 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((25480169510033805 / 2305843009213693952 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2083 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((203841356080270443 / 18446744073709551616 : ℚ) : ℝ) ≤ ((290645213210407 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2084 : ((200681088775376991 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((521 / 16 : ℚ) : ℝ) ∧
    heightZ ((521 / 16 : ℚ) : ℝ) ≤ ((100340544387688497 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((200681088775376991 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((521 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-131 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((521 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-131 / 48 : ℚ) : ℝ) ≤ ((100340544387688497 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2084 : ((70425750021247 / 4503599627370496 : ℚ) : ℝ) ≤ logKernel ((521 / 16 : ℚ) : ℝ) ∧
    logKernel ((521 / 16 : ℚ) : ℝ) ≤ ((1126812000339957 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2084
  constructor
  · exact (show ((70425750021247 / 4503599627370496 : ℚ) : ℝ) ≤ zKernel ((200681088775376991 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((521 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((100340544387688497 / 9223372036854775808 : ℚ) : ℝ) ≤ ((1126812000339957 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2085 : ((197569816873724705 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2085 / 64 : ℚ) : ℝ) ∧
    heightZ ((2085 / 64 : ℚ) : ℝ) ≤ ((49392454218431177 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((197569816873724705 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2085 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-527 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2085 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-527 / 192 : ℚ) : ℝ) ≤ ((49392454218431177 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2085 : ((1092143639736251 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2085 / 64 : ℚ) : ℝ) ∧
    logKernel ((2085 / 64 : ℚ) : ℝ) ≤ ((17064744370879 / 1125899906842624 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2085
  constructor
  · exact (show ((1092143639736251 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((197569816873724705 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2085 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((49392454218431177 / 4611686018427387904 : ℚ) : ℝ) ≤ ((17064744370879 / 1125899906842624 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2086 : ((194506780771992989 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1043 / 32 : ℚ) : ℝ) ∧
    heightZ ((1043 / 32 : ℚ) : ℝ) ≤ ((6078336899124781 / 576460752303423488 : ℚ) : ℝ) := by
  have h : ((194506780771992989 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1043 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-265 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1043 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-265 / 96 : ℚ) : ℝ) ≤ ((6078336899124781 / 576460752303423488 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2086 : ((529270956227167 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((1043 / 32 : ℚ) : ℝ) ∧
    logKernel ((1043 / 32 : ℚ) : ℝ) ≤ ((1058541912454339 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2086
  constructor
  · exact (show ((529270956227167 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((194506780771992989 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1043 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((6078336899124781 / 576460752303423488 : ℚ) : ℝ) ≤ ((1058541912454339 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2087 : ((191491232643419179 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2087 / 64 : ℚ) : ℝ) ∧
    heightZ ((2087 / 64 : ℚ) : ℝ) ≤ ((95745616321709591 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((191491232643419179 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2087 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-533 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2087 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-533 / 192 : ℚ) : ℝ) ≤ ((95745616321709591 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2087 : ((1025974001636889 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2087 / 64 : ℚ) : ℝ) ∧
    logKernel ((2087 / 64 : ℚ) : ℝ) ≤ ((512987000818447 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2087
  constructor
  · exact (show ((1025974001636889 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((191491232643419179 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2087 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((95745616321709591 / 9223372036854775808 : ℚ) : ℝ) ≤ ((512987000818447 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2088 : ((188522436255219935 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((261 / 8 : ℚ) : ℝ) ∧
    heightZ ((261 / 8 : ℚ) : ℝ) ≤ ((94261218127609969 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((188522436255219935 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((261 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-67 / 24 : ℚ) : ℝ) ∧
      Real.exp (-((261 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-67 / 24 : ℚ) : ℝ) ≤ ((94261218127609969 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2088 : ((124301012511895 / 9007199254740992 : ℚ) : ℝ) ≤ logKernel ((261 / 8 : ℚ) : ℝ) ∧
    logKernel ((261 / 8 : ℚ) : ℝ) ≤ ((994408100095165 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2088
  constructor
  · exact (show ((124301012511895 / 9007199254740992 : ℚ) : ℝ) ≤ zKernel ((188522436255219935 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((261 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((94261218127609969 / 9223372036854775808 : ℚ) : ℝ) ≤ ((994408100095165 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2089 : ((185599666788843255 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2089 / 64 : ℚ) : ℝ) ∧
    heightZ ((2089 / 64 : ℚ) : ℝ) ≤ ((92799833394421629 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((185599666788843255 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2089 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-539 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2089 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-539 / 192 : ℚ) : ℝ) ≤ ((92799833394421629 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2089 : ((240953344811177 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((2089 / 64 : ℚ) : ℝ) ∧
    logKernel ((2089 / 64 : ℚ) : ℝ) ≤ ((963813379244713 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2089
  constructor
  · exact (show ((240953344811177 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((185599666788843255 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2089 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((92799833394421629 / 9223372036854775808 : ℚ) : ℝ) ≤ ((963813379244713 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2090 : ((91361105331503607 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((1045 / 32 : ℚ) : ℝ) ∧
    heightZ ((1045 / 32 : ℚ) : ℝ) ≤ ((182722210663007217 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((91361105331503607 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((1045 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-271 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1045 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-271 / 96 : ℚ) : ℝ) ≤ ((182722210663007217 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2090 : ((934159958996923 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1045 / 32 : ℚ) : ℝ) ∧
    logKernel ((1045 / 32 : ℚ) : ℝ) ≤ ((14596249359327 / 1125899906842624 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2090
  constructor
  · exact (show ((934159958996923 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((91361105331503607 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1045 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((182722210663007217 / 18446744073709551616 : ℚ) : ℝ) ≤ ((14596249359327 / 1125899906842624 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2091 : ((89944682679741123 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2091 / 64 : ℚ) : ℝ) ∧
    heightZ ((2091 / 64 : ℚ) : ℝ) ≤ ((179889365359482249 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((89944682679741123 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2091 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-545 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2091 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-545 / 192 : ℚ) : ℝ) ≤ ((179889365359482249 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2091 : ((905418878576877 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2091 / 64 : ℚ) : ℝ) ∧
    logKernel ((2091 / 64 : ℚ) : ℝ) ≤ ((452709439288441 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2091
  constructor
  · exact (show ((905418878576877 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((89944682679741123 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2091 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((179889365359482249 / 18446744073709551616 : ℚ) : ℝ) ≤ ((452709439288441 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2092 : ((88550219625787205 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((523 / 16 : ℚ) : ℝ) ∧
    heightZ ((523 / 16 : ℚ) : ℝ) ≤ ((177100439251574413 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((88550219625787205 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((523 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-137 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((523 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-137 / 48 : ℚ) : ℝ) ≤ ((177100439251574413 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2092 : ((438781034119505 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((523 / 16 : ℚ) : ℝ) ∧
    logKernel ((523 / 16 : ℚ) : ℝ) ≤ ((877562068239015 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2092
  constructor
  · exact (show ((438781034119505 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((88550219625787205 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((523 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((177100439251574413 / 18446744073709551616 : ℚ) : ℝ) ≤ ((877562068239015 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2093 : ((21794343929408473 / 2305843009213693952 : ℚ) : ℝ) ≤ heightZ ((2093 / 64 : ℚ) : ℝ) ∧
    heightZ ((2093 / 64 : ℚ) : ℝ) ≤ ((174354751435267787 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((21794343929408473 / 2305843009213693952 : ℚ) : ℝ) ≤ Real.exp (-((2093 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-551 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2093 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-551 / 192 : ℚ) : ℝ) ≤ ((174354751435267787 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2093 : ((425281160926523 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2093 / 64 : ℚ) : ℝ) ∧
    logKernel ((2093 / 64 : ℚ) : ℝ) ≤ ((850562321853051 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2093
  constructor
  · exact (show ((425281160926523 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((21794343929408473 / 2305843009213693952 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2093 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((174354751435267787 / 18446744073709551616 : ℚ) : ℝ) ≤ ((850562321853051 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2094 : ((171651631562984751 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1047 / 32 : ℚ) : ℝ) ∧
    heightZ ((1047 / 32 : ℚ) : ℝ) ≤ ((85825815781492377 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((171651631562984751 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1047 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-277 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1047 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-277 / 96 : ℚ) : ℝ) ≤ ((85825815781492377 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2094 : ((824393270333337 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1047 / 32 : ℚ) : ℝ) ∧
    logKernel ((1047 / 32 : ℚ) : ℝ) ≤ ((412196635166671 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2094
  constructor
  · exact (show ((824393270333337 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((171651631562984751 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1047 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((85825815781492377 / 9223372036854775808 : ℚ) : ℝ) ≤ ((412196635166671 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2095 : ((84495209839961795 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2095 / 64 : ℚ) : ℝ) ∧
    heightZ ((2095 / 64 : ℚ) : ℝ) ≤ ((168990419679923593 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((84495209839961795 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2095 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-557 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2095 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-557 / 192 : ℚ) : ℝ) ≤ ((168990419679923593 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2095 : ((799029355885711 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2095 / 64 : ℚ) : ℝ) ∧
    logKernel ((2095 / 64 : ℚ) : ℝ) ≤ ((199757338971429 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2095
  constructor
  · exact (show ((799029355885711 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((84495209839961795 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2095 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((168990419679923593 / 18446744073709551616 : ℚ) : ℝ) ≤ ((199757338971429 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2096 : ((10398154128933339 / 1152921504606846976 : ℚ) : ℝ) ≤ heightZ ((131 / 4 : ℚ) : ℝ) ∧
    heightZ ((131 / 4 : ℚ) : ℝ) ≤ ((166370466062933427 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((10398154128933339 / 1152921504606846976 : ℚ) : ℝ) ≤ Real.exp (-((131 / 4 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-35 / 12 : ℚ) : ℝ) ∧
      Real.exp (-((131 / 4 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-35 / 12 : ℚ) : ℝ) ≤ ((166370466062933427 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2096 : ((387222903523329 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((131 / 4 : ℚ) : ℝ) ∧
    logKernel ((131 / 4 : ℚ) : ℝ) ≤ ((774445807046663 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2096
  constructor
  · exact (show ((387222903523329 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((10398154128933339 / 1152921504606846976 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((131 / 4 : ℚ) : ℝ)) hh).trans
      (show zKernel ((166370466062933427 / 18446744073709551616 : ℚ) : ℝ) ≤ ((774445807046663 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

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

theorem log_height_bounds_224 : ((62590785621528599 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((1033 / 32 : ℚ) : ℝ) ∧
    Real.log ((1033 / 32 : ℚ) : ℝ) ≤ ((250363142486114399 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((62590785621528599 / 18014398509481984 : ℚ) : ℝ) ≤ ((1033 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1033 / 32 : ℚ) : ℝ) ≤ Real.exp ((250363142486114399 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_224 : heightPower (224 : Fin 988) ≤ ((508781721968161 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_224
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_224 : heightFactor (224 : Fin 988) ≤ ((53293886649175 / 8796093022208 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_224
  obtain ⟨hpl, hph⟩ := kernel_bounds_2065
  obtain ⟨hcl, hch⟩ := kernel_bounds_2066
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2066
  have h : (((1067089 / 512 : ℚ) : ℝ) * (logKernel ((2065 / 64 : ℚ) : ℝ) - logKernel ((1033 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1033 / 32 : ℚ) : ℝ) + Real.log ((1033 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((53293886649175 / 8796093022208 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_225 : ((62599502969150673 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((2067 / 64 : ℚ) : ℝ) ∧
    Real.log ((2067 / 64 : ℚ) : ℝ) ≤ ((250398011876602695 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((62599502969150673 / 18014398509481984 : ℚ) : ℝ) ≤ ((2067 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2067 / 64 : ℚ) : ℝ) ≤ Real.exp ((250398011876602695 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_225 : heightPower (225 : Fin 988) ≤ ((1022097699004021 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_225
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_225 : heightFactor (225 : Fin 988) ≤ ((831721630817059 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_225
  obtain ⟨hpl, hph⟩ := kernel_bounds_2066
  obtain ⟨hcl, hch⟩ := kernel_bounds_2067
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2067
  have h : (((4272489 / 2048 : ℚ) : ℝ) * (logKernel ((1033 / 32 : ℚ) : ℝ) - logKernel ((2067 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2067 / 64 : ℚ) : ℝ) + Real.log ((2067 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((831721630817059 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_226 : ((125216432200802605 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((517 / 16 : ℚ) : ℝ) ∧
    Real.log ((517 / 16 : ℚ) : ℝ) ≤ ((250432864401605213 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((125216432200802605 / 36028797018963968 : ℚ) : ℝ) ≤ ((517 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((517 / 16 : ℚ) : ℝ) ≤ Real.exp ((250432864401605213 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_226 : heightPower (226 : Fin 988) ≤ ((256657972047729 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_226
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_226 : heightFactor (226 : Fin 988) ≤ ((1622513708588243 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_226
  obtain ⟨hpl, hph⟩ := kernel_bounds_2067
  obtain ⟨hcl, hch⟩ := kernel_bounds_2068
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2068
  have h : (((267289 / 128 : ℚ) : ℝ) * (logKernel ((2067 / 64 : ℚ) : ℝ) - logKernel ((517 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((517 / 16 : ℚ) : ℝ) + Real.log ((517 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1622513708588243 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_227 : ((125233850038714461 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2069 / 64 : ℚ) : ℝ) ∧
    Real.log ((2069 / 64 : ℚ) : ℝ) ≤ ((250467700077428925 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((125233850038714461 / 36028797018963968 : ℚ) : ℝ) ≤ ((2069 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2069 / 64 : ℚ) : ℝ) ≤ Real.exp ((250467700077428925 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_227 : heightPower (227 : Fin 988) ≤ ((515583005780353 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_227
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_227 : heightFactor (227 : Fin 988) ≤ ((791295188405393 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_227
  obtain ⟨hpl, hph⟩ := kernel_bounds_2068
  obtain ⟨hcl, hch⟩ := kernel_bounds_2069
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2069
  have h : (((4280761 / 2048 : ℚ) : ℝ) * (logKernel ((517 / 16 : ℚ) : ℝ) - logKernel ((2069 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2069 / 64 : ℚ) : ℝ) + Real.log ((2069 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((791295188405393 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_228 : ((250502518920357161 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1035 / 32 : ℚ) : ℝ) ∧
    Real.log ((1035 / 32 : ℚ) : ℝ) ≤ ((62625629730089291 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((250502518920357161 / 72057594037927936 : ℚ) : ℝ) ≤ ((1035 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1035 / 32 : ℚ) : ℝ) ≤ Real.exp ((62625629730089291 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_228 : heightPower (228 : Fin 988) ≤ ((1035700069176999 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_228
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_228 : heightFactor (228 : Fin 988) ≤ ((1543648551212819 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_228
  obtain ⟨hpl, hph⟩ := kernel_bounds_2069
  obtain ⟨hcl, hch⟩ := kernel_bounds_2070
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2070
  have h : (((1071225 / 512 : ℚ) : ℝ) * (logKernel ((2069 / 64 : ℚ) : ℝ) - logKernel ((1035 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1035 / 32 : ℚ) : ℝ) + Real.log ((1035 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1543648551212819 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_229 : ((250537320946649669 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2071 / 64 : ℚ) : ℝ) ∧
    Real.log ((2071 / 64 : ℚ) : ℝ) ≤ ((31317165118331209 / 9007199254740992 : ℚ) : ℝ) := by
  have hl : Real.exp ((250537320946649669 / 72057594037927936 : ℚ) : ℝ) ≤ ((2071 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2071 / 64 : ℚ) : ℝ) ≤ Real.exp ((31317165118331209 / 9007199254740992 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_229 : heightPower (229 : Fin 988) ≤ ((260058515275827 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_229
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_229 : heightFactor (229 : Fin 988) ≤ ((188208015399975 / 35184372088832 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_229
  obtain ⟨hpl, hph⟩ := kernel_bounds_2070
  obtain ⟨hcl, hch⟩ := kernel_bounds_2071
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2071
  have h : (((4289041 / 2048 : ℚ) : ℝ) * (logKernel ((1035 / 32 : ℚ) : ℝ) - logKernel ((2071 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2071 / 64 : ℚ) : ℝ) + Real.log ((2071 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((188208015399975 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_230 : ((125286053086271319 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((259 / 8 : ℚ) : ℝ) ∧
    Real.log ((259 / 8 : ℚ) : ℝ) ≤ ((250572106172542641 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((125286053086271319 / 36028797018963968 : ℚ) : ℝ) ≤ ((259 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((259 / 8 : ℚ) : ℝ) ≤ Real.exp ((250572106172542641 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_230 : heightPower (230 : Fin 988) ≤ ((65297999212691 / 17592186044416 : ℚ) : ℝ) := by
  have hh := log_height_bounds_230
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_230 : heightFactor (230 : Fin 988) ≤ ((734306787901489 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_230
  obtain ⟨hpl, hph⟩ := kernel_bounds_2071
  obtain ⟨hcl, hch⟩ := kernel_bounds_2072
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2072
  have h : (((67081 / 32 : ℚ) : ℝ) * (logKernel ((2071 / 64 : ℚ) : ℝ) - logKernel ((259 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((259 / 8 : ℚ) : ℝ) + Real.log ((259 / 8 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((734306787901489 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_231 : ((125303437307124379 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2073 / 64 : ℚ) : ℝ) ∧
    Real.log ((2073 / 64 : ℚ) : ℝ) ≤ ((250606874614248761 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((125303437307124379 / 36028797018963968 : ℚ) : ℝ) ≤ ((2073 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2073 / 64 : ℚ) : ℝ) ≤ Real.exp ((250606874614248761 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_231 : heightPower (231 : Fin 988) ≤ ((1049301848139575 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_231
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_231 : heightFactor (231 : Fin 988) ≤ ((1432473969174941 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_231
  obtain ⟨hpl, hph⟩ := kernel_bounds_2072
  obtain ⟨hcl, hch⟩ := kernel_bounds_2073
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2073
  have h : (((4297329 / 2048 : ℚ) : ℝ) * (logKernel ((259 / 8 : ℚ) : ℝ) - logKernel ((2073 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2073 / 64 : ℚ) : ℝ) + Real.log ((2073 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1432473969174941 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_232 : ((15665101642997329 / 4503599627370496 : ℚ) : ℝ) ≤ Real.log ((1037 / 32 : ℚ) : ℝ) ∧
    Real.log ((1037 / 32 : ℚ) : ℝ) ≤ ((250641626287957267 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((15665101642997329 / 4503599627370496 : ℚ) : ℝ) ≤ ((1037 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1037 / 32 : ℚ) : ℝ) ≤ Real.exp ((250641626287957267 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_232 : heightPower (232 : Fin 988) ≤ ((1053835643376103 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_232
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_232 : heightFactor (232 : Fin 988) ≤ ((349305731610099 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_232
  obtain ⟨hpl, hph⟩ := kernel_bounds_2073
  obtain ⟨hcl, hch⟩ := kernel_bounds_2074
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2074
  have h : (((1075369 / 512 : ℚ) : ℝ) * (logKernel ((2073 / 64 : ℚ) : ℝ) - logKernel ((1037 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1037 / 32 : ℚ) : ℝ) + Real.log ((1037 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((349305731610099 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_233 : ((250676361209833977 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2075 / 64 : ℚ) : ℝ) ∧
    Real.log ((2075 / 64 : ℚ) : ℝ) ≤ ((62669090302458495 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((250676361209833977 / 72057594037927936 : ℚ) : ℝ) ≤ ((2075 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2075 / 64 : ℚ) : ℝ) ≤ Real.exp ((62669090302458495 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_233 : heightPower (233 : Fin 988) ≤ ((1058369373175787 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_233
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_233 : heightFactor (233 : Fin 988) ≤ ((681419309946751 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_233
  obtain ⟨hpl, hph⟩ := kernel_bounds_2074
  obtain ⟨hcl, hch⟩ := kernel_bounds_2075
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2075
  have h : (((4305625 / 2048 : ℚ) : ℝ) * (logKernel ((1037 / 32 : ℚ) : ℝ) - logKernel ((2075 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2075 / 64 : ℚ) : ℝ) + Real.log ((2075 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((681419309946751 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_234 : ((31338884924502669 / 9007199254740992 : ℚ) : ℝ) ≤ Real.log ((519 / 16 : ℚ) : ℝ) ∧
    Real.log ((519 / 16 : ℚ) : ℝ) ≤ ((250711079396021355 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((31338884924502669 / 9007199254740992 : ℚ) : ℝ) ≤ ((519 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((519 / 16 : ℚ) : ℝ) ≤ Real.exp ((250711079396021355 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_234 : heightPower (234 : Fin 988) ≤ ((531451518800843 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_234
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_234 : heightFactor (234 : Fin 988) ≤ ((166162469691657 / 35184372088832 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_234
  obtain ⟨hpl, hph⟩ := kernel_bounds_2075
  obtain ⟨hcl, hch⟩ := kernel_bounds_2076
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2076
  have h : (((269361 / 128 : ℚ) : ℝ) * (logKernel ((2075 / 64 : ℚ) : ℝ) - logKernel ((519 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((519 / 16 : ℚ) : ℝ) + Real.log ((519 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((166162469691657 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_235 : ((250745780862638523 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2077 / 64 : ℚ) : ℝ) ∧
    Real.log ((2077 / 64 : ℚ) : ℝ) ≤ ((125372890431319263 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((250745780862638523 / 72057594037927936 : ℚ) : ℝ) ≤ ((2077 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2077 / 64 : ℚ) : ℝ) ≤ Real.exp ((125372890431319263 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_235 : heightPower (235 : Fin 988) ≤ ((1067436636716763 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_235
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_235 : heightFactor (235 : Fin 988) ≤ ((1296585569928683 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_235
  obtain ⟨hpl, hph⟩ := kernel_bounds_2076
  obtain ⟨hcl, hch⟩ := kernel_bounds_2077
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2077
  have h : (((4313929 / 2048 : ℚ) : ℝ) * (logKernel ((519 / 16 : ℚ) : ℝ) - logKernel ((2077 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2077 / 64 : ℚ) : ℝ) + Real.log ((2077 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1296585569928683 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_236 : ((250780465625781345 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1039 / 32 : ℚ) : ℝ) ∧
    Real.log ((1039 / 32 : ℚ) : ℝ) ≤ ((62695116406445337 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((250780465625781345 / 72057594037927936 : ℚ) : ℝ) ≤ ((1039 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1039 / 32 : ℚ) : ℝ) ≤ Real.exp ((62695116406445337 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_236 : heightPower (236 : Fin 988) ≤ ((535985085291947 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_236
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_236 : heightFactor (236 : Fin 988) ≤ ((1264675797405749 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_236
  obtain ⟨hpl, hph⟩ := kernel_bounds_2077
  obtain ⟨hcl, hch⟩ := kernel_bounds_2078
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2078
  have h : (((1079521 / 512 : ℚ) : ℝ) * (logKernel ((2077 / 64 : ℚ) : ℝ) - logKernel ((1039 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1039 / 32 : ℚ) : ℝ) + Real.log ((1039 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1264675797405749 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_237 : ((250815133701522445 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2079 / 64 : ℚ) : ℝ) ∧
    Real.log ((2079 / 64 : ℚ) : ℝ) ≤ ((15675945856345153 / 4503599627370496 : ℚ) : ℝ) := by
  have hl : Real.exp ((250815133701522445 / 72057594037927936 : ℚ) : ℝ) ≤ ((2079 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2079 / 64 : ℚ) : ℝ) ≤ Real.exp ((15675945856345153 / 4503599627370496 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_237 : heightPower (237 : Fin 988) ≤ ((538251819632931 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_237
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_237 : heightFactor (237 : Fin 988) ≤ ((1233550677548125 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_237
  obtain ⟨hpl, hph⟩ := kernel_bounds_2078
  obtain ⟨hcl, hch⟩ := kernel_bounds_2079
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2079
  have h : (((4322241 / 2048 : ℚ) : ℝ) * (logKernel ((1039 / 32 : ℚ) : ℝ) - logKernel ((2079 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2079 / 64 : ℚ) : ℝ) + Real.log ((2079 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1233550677548125 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_238 : ((250849785105911259 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((65 / 2 : ℚ) : ℝ) ∧
    Real.log ((65 / 2 : ℚ) : ℝ) ≤ ((125424892552955631 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((250849785105911259 / 72057594037927936 : ℚ) : ℝ) ≤ ((65 / 2 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((65 / 2 : ℚ) : ℝ) ≤ Real.exp ((125424892552955631 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_238 : heightPower (238 : Fin 988) ≤ ((1081037042825359 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_238
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_238 : heightFactor (238 : Fin 988) ≤ ((300797733251031 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_238
  obtain ⟨hpl, hph⟩ := kernel_bounds_2079
  obtain ⟨hcl, hch⟩ := kernel_bounds_2080
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2080
  have h : (((4225 / 2 : ℚ) : ℝ) * (logKernel ((2079 / 64 : ℚ) : ℝ) - logKernel ((65 / 2 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((65 / 2 : ℚ) : ℝ) + Real.log ((65 / 2 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((300797733251031 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_239 : ((250884419854974083 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2081 / 64 : ℚ) : ℝ) ∧
    Real.log ((2081 / 64 : ℚ) : ℝ) ≤ ((125442209927487043 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((250884419854974083 / 72057594037927936 : ℚ) : ℝ) ≤ ((2081 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2081 / 64 : ℚ) : ℝ) ≤ Real.exp ((125442209927487043 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_239 : heightPower (239 : Fin 988) ≤ ((542785190662495 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_239
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_239 : heightFactor (239 : Fin 988) ≤ ((1173577759592321 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_239
  obtain ⟨hpl, hph⟩ := kernel_bounds_2080
  obtain ⟨hcl, hch⟩ := kernel_bounds_2081
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2081
  have h : (((4330561 / 2048 : ℚ) : ℝ) * (logKernel ((65 / 2 : ℚ) : ℝ) - logKernel ((2081 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2081 / 64 : ℚ) : ℝ) + Real.log ((2081 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1173577759592321 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_240 : ((250919037964714113 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1041 / 32 : ℚ) : ℝ) ∧
    Real.log ((1041 / 32 : ℚ) : ℝ) ≤ ((62729759491178529 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((250919037964714113 / 72057594037927936 : ℚ) : ℝ) ≤ ((1041 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1041 / 32 : ℚ) : ℝ) ≤ Real.exp ((62729759491178529 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_240 : heightPower (240 : Fin 988) ≤ ((545051827413633 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_240
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_240 : heightFactor (240 : Fin 988) ≤ ((1144692814698543 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_240
  obtain ⟨hpl, hph⟩ := kernel_bounds_2081
  obtain ⟨hcl, hch⟩ := kernel_bounds_2082
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2082
  have h : (((1083681 / 512 : ℚ) : ℝ) * (logKernel ((2081 / 64 : ℚ) : ℝ) - logKernel ((1041 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1041 / 32 : ℚ) : ℝ) + Real.log ((1041 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1144692814698543 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_241 : ((62738409862777873 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((2083 / 64 : ℚ) : ℝ) ∧
    Real.log ((2083 / 64 : ℚ) : ℝ) ≤ ((250953639451111495 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((62738409862777873 / 18014398509481984 : ℚ) : ℝ) ≤ ((2083 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2083 / 64 : ℚ) : ℝ) ≤ Real.exp ((250953639451111495 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_241 : heightPower (241 : Fin 988) ≤ ((547318431697305 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_241
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_241 : heightFactor (241 : Fin 988) ≤ ((279129551489277 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_241
  obtain ⟨hpl, hph⟩ := kernel_bounds_2082
  obtain ⟨hcl, hch⟩ := kernel_bounds_2083
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2083
  have h : (((4338889 / 2048 : ℚ) : ℝ) * (logKernel ((1041 / 32 : ℚ) : ℝ) - logKernel ((2083 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2083 / 64 : ℚ) : ℝ) + Real.log ((2083 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((279129551489277 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_242 : ((250988224330123353 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((521 / 16 : ℚ) : ℝ) ∧
    Real.log ((521 / 16 : ℚ) : ℝ) ≤ ((62747056082530839 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((250988224330123353 / 72057594037927936 : ℚ) : ℝ) ≤ ((521 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((521 / 16 : ℚ) : ℝ) ≤ Real.exp ((62747056082530839 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_242 : heightPower (242 : Fin 988) ≤ ((549585003544677 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_242
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_242 : heightFactor (242 : Fin 988) ≤ ((1089036480209337 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_242
  obtain ⟨hpl, hph⟩ := kernel_bounds_2083
  obtain ⟨hcl, hch⟩ := kernel_bounds_2084
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2084
  have h : (((271441 / 128 : ℚ) : ℝ) * (logKernel ((2083 / 64 : ℚ) : ℝ) - logKernel ((521 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((521 / 16 : ℚ) : ℝ) + Real.log ((521 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1089036480209337 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_243 : ((31377849077210483 / 9007199254740992 : ℚ) : ℝ) ≤ Real.log ((2085 / 64 : ℚ) : ℝ) ∧
    Real.log ((2085 / 64 : ℚ) : ℝ) ≤ ((251022792617683867 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((31377849077210483 / 9007199254740992 : ℚ) : ℝ) ≤ ((2085 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2085 / 64 : ℚ) : ℝ) ≤ Real.exp ((251022792617683867 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_243 : heightPower (243 : Fin 988) ≤ ((1103703085973741 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_243
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_243 : heightFactor (243 : Fin 988) ≤ ((132778826591573 / 35184372088832 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_243
  obtain ⟨hpl, hph⟩ := kernel_bounds_2084
  obtain ⟨hcl, hch⟩ := kernel_bounds_2085
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2085
  have h : (((4347225 / 2048 : ℚ) : ℝ) * (logKernel ((521 / 16 : ℚ) : ℝ) - logKernel ((2085 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2085 / 64 : ℚ) : ℝ) + Real.log ((2085 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((132778826591573 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_244 : ((15691084020606517 / 4503599627370496 : ℚ) : ℝ) ≤ Real.log ((1043 / 32 : ℚ) : ℝ) ∧
    Real.log ((1043 / 32 : ℚ) : ℝ) ≤ ((251057344329704275 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((15691084020606517 / 4503599627370496 : ℚ) : ℝ) ≤ ((1043 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1043 / 32 : ℚ) : ℝ) ≤ Real.exp ((251057344329704275 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_244 : heightPower (244 : Fin 988) ≤ ((1108236100109925 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_244
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_244 : heightFactor (244 : Fin 988) ≤ ((518041998366565 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_244
  obtain ⟨hpl, hph⟩ := kernel_bounds_2085
  obtain ⟨hcl, hch⟩ := kernel_bounds_2086
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2086
  have h : (((1087849 / 512 : ℚ) : ℝ) * (logKernel ((2085 / 64 : ℚ) : ℝ) - logKernel ((1043 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1043 / 32 : ℚ) : ℝ) + Real.log ((1043 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((518041998366565 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_245 : ((251091879482072945 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2087 / 64 : ℚ) : ℝ) ∧
    Real.log ((2087 / 64 : ℚ) : ℝ) ≤ ((62772969870518237 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((251091879482072945 / 72057594037927936 : ℚ) : ℝ) ≤ ((2087 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2087 / 64 : ℚ) : ℝ) ≤ Real.exp ((62772969870518237 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_245 : heightPower (245 : Fin 988) ≤ ((1112769049559969 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_245
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_245 : heightFactor (245 : Fin 988) ≤ ((505290216548255 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_245
  obtain ⟨hpl, hph⟩ := kernel_bounds_2086
  obtain ⟨hcl, hch⟩ := kernel_bounds_2087
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2087
  have h : (((4355569 / 2048 : ℚ) : ℝ) * (logKernel ((1043 / 32 : ℚ) : ℝ) - logKernel ((2087 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2087 / 64 : ℚ) : ℝ) + Real.log ((2087 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((505290216548255 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_246 : ((62781599522663855 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((261 / 8 : ℚ) : ℝ) ∧
    Real.log ((261 / 8 : ℚ) : ℝ) ≤ ((251126398090655423 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((62781599522663855 / 18014398509481984 : ℚ) : ℝ) ≤ ((261 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((261 / 8 : ℚ) : ℝ) ≤ Real.exp ((251126398090655423 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_246 : heightPower (246 : Fin 988) ≤ ((139662741798231 / 35184372088832 : ℚ) : ℝ) := by
  have hh := log_height_bounds_246
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_246 : heightFactor (246 : Fin 988) ≤ ((492852060194481 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_246
  obtain ⟨hpl, hph⟩ := kernel_bounds_2087
  obtain ⟨hcl, hch⟩ := kernel_bounds_2088
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2088
  have h : (((68121 / 32 : ℚ) : ℝ) * (logKernel ((2087 / 64 : ℚ) : ℝ) - logKernel ((261 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((261 / 8 : ℚ) : ℝ) + Real.log ((261 / 8 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((492852060194481 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_247 : ((125580450085647221 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2089 / 64 : ℚ) : ℝ) ∧
    Real.log ((2089 / 64 : ℚ) : ℝ) ≤ ((251160900171294445 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((125580450085647221 / 36028797018963968 : ℚ) : ℝ) ≤ ((2089 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2089 / 64 : ℚ) : ℝ) ≤ Real.exp ((251160900171294445 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_247 : heightPower (247 : Fin 988) ≤ ((140229344331181 / 35184372088832 : ℚ) : ℝ) := by
  have hh := log_height_bounds_247
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_247 : heightFactor (247 : Fin 988) ≤ ((961439645103841 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_247
  obtain ⟨hpl, hph⟩ := kernel_bounds_2088
  obtain ⟨hcl, hch⟩ := kernel_bounds_2089
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2089
  have h : (((4363921 / 2048 : ℚ) : ℝ) * (logKernel ((261 / 8 : ℚ) : ℝ) - logKernel ((2089 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2089 / 64 : ℚ) : ℝ) + Real.log ((2089 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((961439645103841 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_248 : ((125597692869905005 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((1045 / 32 : ℚ) : ℝ) ∧
    Real.log ((1045 / 32 : ℚ) : ℝ) ≤ ((251195385739810013 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((125597692869905005 / 36028797018963968 : ℚ) : ℝ) ≤ ((1045 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1045 / 32 : ℚ) : ℝ) ≤ Real.exp ((251195385739810013 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_248 : heightPower (248 : Fin 988) ≤ ((563183755206283 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_248
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_248 : heightFactor (248 : Fin 988) ≤ ((937771972147029 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_248
  obtain ⟨hpl, hph⟩ := kernel_bounds_2089
  obtain ⟨hcl, hch⟩ := kernel_bounds_2090
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2090
  have h : (((1092025 / 512 : ℚ) : ℝ) * (logKernel ((2089 / 64 : ℚ) : ℝ) - logKernel ((1045 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1045 / 32 : ℚ) : ℝ) + Real.log ((1045 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((937771972147029 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_249 : ((251229854811999421 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2091 / 64 : ℚ) : ℝ) ∧
    Real.log ((2091 / 64 : ℚ) : ℝ) ≤ ((3925466481437491 / 1125899906842624 : ℚ) : ℝ) := by
  have hl : Real.exp ((251229854811999421 / 72057594037927936 : ℚ) : ℝ) ≤ ((2091 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2091 / 64 : ℚ) : ℝ) ≤ Real.exp ((3925466481437491 / 1125899906842624 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_249 : heightPower (249 : Fin 988) ≤ ((565450100868455 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_249
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_249 : heightFactor (249 : Fin 988) ≤ ((457343217777733 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_249
  obtain ⟨hpl, hph⟩ := kernel_bounds_2090
  obtain ⟨hcl, hch⟩ := kernel_bounds_2091
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2091
  have h : (((4372281 / 2048 : ℚ) : ℝ) * (logKernel ((1045 / 32 : ℚ) : ℝ) - logKernel ((2091 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2091 / 64 : ℚ) : ℝ) + Real.log ((2091 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((457343217777733 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_250 : ((251264307403637313 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((523 / 16 : ℚ) : ℝ) ∧
    Real.log ((523 / 16 : ℚ) : ℝ) ≤ ((62816076850909329 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((251264307403637313 / 72057594037927936 : ℚ) : ℝ) ≤ ((523 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((523 / 16 : ℚ) : ℝ) ≤ Real.exp ((62816076850909329 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_250 : heightPower (250 : Fin 988) ≤ ((283858207171025 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_250
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_250 : heightFactor (250 : Fin 988) ≤ ((892168729443101 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_250
  obtain ⟨hpl, hph⟩ := kernel_bounds_2091
  obtain ⟨hcl, hch⟩ := kernel_bounds_2092
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2092
  have h : (((273529 / 128 : ℚ) : ℝ) * (logKernel ((2091 / 64 : ℚ) : ℝ) - logKernel ((523 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((523 / 16 : ℚ) : ℝ) + Real.log ((523 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((892168729443101 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_251 : ((251298743530475707 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2093 / 64 : ℚ) : ℝ) ∧
    Real.log ((2093 / 64 : ℚ) : ℝ) ≤ ((125649371765237855 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((251298743530475707 / 72057594037927936 : ℚ) : ℝ) ≤ ((2093 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2093 / 64 : ℚ) : ℝ) ≤ Real.exp ((125649371765237855 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_251 : heightPower (251 : Fin 988) ≤ ((569982695657833 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_251
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_251 : heightFactor (251 : Fin 988) ≤ ((870204899168717 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_251
  obtain ⟨hpl, hph⟩ := kernel_bounds_2092
  obtain ⟨hcl, hch⟩ := kernel_bounds_2093
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2093
  have h : (((4380649 / 2048 : ℚ) : ℝ) * (logKernel ((523 / 16 : ℚ) : ℝ) - logKernel ((2093 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2093 / 64 : ℚ) : ℝ) + Real.log ((2093 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((870204899168717 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_252 : ((251333163208244051 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1047 / 32 : ℚ) : ℝ) ∧
    Real.log ((1047 / 32 : ℚ) : ℝ) ≤ ((125666581604122027 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((251333163208244051 / 72057594037927936 : ℚ) : ℝ) ≤ ((1047 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1047 / 32 : ℚ) : ℝ) ≤ Real.exp ((125666581604122027 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_252 : heightPower (252 : Fin 988) ≤ ((1144497889693053 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_252
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_252 : heightFactor (252 : Fin 988) ≤ ((424390666360081 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_252
  obtain ⟨hpl, hph⟩ := kernel_bounds_2093
  obtain ⟨hcl, hch⟩ := kernel_bounds_2094
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2094
  have h : (((1096209 / 512 : ℚ) : ℝ) * (logKernel ((2093 / 64 : ℚ) : ℝ) - logKernel ((1047 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1047 / 32 : ℚ) : ℝ) + Real.log ((1047 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((424390666360081 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_253 : ((251367566452649265 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2095 / 64 : ℚ) : ℝ) ∧
    Real.log ((2095 / 64 : ℚ) : ℝ) ≤ ((62841891613162317 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((251367566452649265 / 72057594037927936 : ℚ) : ℝ) ≤ ((2095 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2095 / 64 : ℚ) : ℝ) ≤ Real.exp ((62841891613162317 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_253 : heightPower (253 : Fin 988) ≤ ((1149030323877615 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_253
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_253 : heightFactor (253 : Fin 988) ≤ ((25871398509679 / 8796093022208 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_253
  obtain ⟨hpl, hph⟩ := kernel_bounds_2094
  obtain ⟨hcl, hch⟩ := kernel_bounds_2095
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2095
  have h : (((4389025 / 2048 : ℚ) : ℝ) * (logKernel ((1047 / 32 : ℚ) : ℝ) - logKernel ((2095 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2095 / 64 : ℚ) : ℝ) + Real.log ((2095 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((25871398509679 / 8796093022208 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_254 : ((125700976639687891 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((131 / 4 : ℚ) : ℝ) ∧
    Real.log ((131 / 4 : ℚ) : ℝ) ≤ ((251401953279375785 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((125700976639687891 / 36028797018963968 : ℚ) : ℝ) ≤ ((131 / 4 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((131 / 4 : ℚ) : ℝ) ≤ Real.exp ((251401953279375785 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_254 : heightPower (254 : Fin 988) ≤ ((1153562693930619 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_254
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_254 : heightFactor (254 : Fin 988) ≤ ((403751103087737 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_254
  obtain ⟨hpl, hph⟩ := kernel_bounds_2095
  obtain ⟨hcl, hch⟩ := kernel_bounds_2096
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2096
  have h : (((17161 / 8 : ℚ) : ℝ) * (logKernel ((2095 / 64 : ℚ) : ℝ) - logKernel ((131 / 4 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((131 / 4 : ℚ) : ℝ) + Real.log ((131 / 4 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((403751103087737 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_255 : ((251436323704085589 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2097 / 64 : ℚ) : ℝ) ∧
    Real.log ((2097 / 64 : ℚ) : ℝ) ≤ ((31429540463010699 / 9007199254740992 : ℚ) : ℝ) := by
  have hl : Real.exp ((251436323704085589 / 72057594037927936 : ℚ) : ℝ) ≤ ((2097 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2097 / 64 : ℚ) : ℝ) ≤ Real.exp ((31429540463010699 / 9007199254740992 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_255 : heightPower (255 : Fin 988) ≤ ((579047499956623 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_255
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_255 : heightFactor (255 : Fin 988) ≤ ((787621060583481 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_255
  obtain ⟨hpl, hph⟩ := kernel_bounds_2096
  obtain ⟨hcl, hch⟩ := kernel_bounds_2097
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2097
  have h : (((4397409 / 2048 : ℚ) : ℝ) * (logKernel ((131 / 4 : ℚ) : ℝ) - logKernel ((2097 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2097 / 64 : ℚ) : ℝ) + Real.log ((2097 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((787621060583481 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

end LegendreK6.M2Pilot.Enclosures.Height007
