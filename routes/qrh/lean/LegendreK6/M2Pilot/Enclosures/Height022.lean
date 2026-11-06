import LegendreK6.M2PilotDefinitions
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp

/-! Generated proposals: every bound is checked by Lean, not by trusting Arb. -/
namespace LegendreK6.M2Pilot.Enclosures.Height022
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem height_z_bounds_2545 : ((74679089266555 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2545 / 64 : ℚ) : ℝ) ∧
    heightZ ((2545 / 64 : ℚ) : ℝ) ≤ ((149358178533113 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((74679089266555 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2545 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1907 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2545 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1907 / 192 : ℚ) : ℝ) ≤ ((149358178533113 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2545 : ((624160933 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2545 / 64 : ℚ) : ℝ) ∧
    logKernel ((2545 / 64 : ℚ) : ℝ) ≤ ((312080469 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2545
  constructor
  · exact (show ((624160933 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((74679089266555 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2545 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((149358178533113 / 18446744073709551616 : ℚ) : ℝ) ≤ ((312080469 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2546 : ((18380324325433 / 2305843009213693952 : ℚ) : ℝ) ≤ heightZ ((1273 / 32 : ℚ) : ℝ) ∧
    heightZ ((1273 / 32 : ℚ) : ℝ) ≤ ((147042594603467 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((18380324325433 / 2305843009213693952 : ℚ) : ℝ) ≤ Real.exp (-((1273 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-955 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1273 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-955 / 96 : ℚ) : ℝ) ≤ ((147042594603467 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2546 : ((604957519 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1273 / 32 : ℚ) : ℝ) ∧
    logKernel ((1273 / 32 : ℚ) : ℝ) ≤ ((151239381 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2546
  constructor
  · exact (show ((604957519 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((18380324325433 / 2305843009213693952 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1273 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((147042594603467 / 18446744073709551616 : ℚ) : ℝ) ≤ ((151239381 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2547 : ((144762910475141 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2547 / 64 : ℚ) : ℝ) ∧
    heightZ ((2547 / 64 : ℚ) : ℝ) ≤ ((18095363809393 / 2305843009213693952 : ℚ) : ℝ) := by
  have h : ((144762910475141 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2547 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1913 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2547 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1913 / 192 : ℚ) : ℝ) ≤ ((18095363809393 / 2305843009213693952 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2547 : ((586344933 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2547 / 64 : ℚ) : ℝ) ∧
    logKernel ((2547 / 64 : ℚ) : ℝ) ≤ ((293172469 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2547
  constructor
  · exact (show ((586344933 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((144762910475141 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2547 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((18095363809393 / 2305843009213693952 : ℚ) : ℝ) ≤ ((293172469 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2548 : ((142518569573309 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((637 / 16 : ℚ) : ℝ) ∧
    heightZ ((637 / 16 : ℚ) : ℝ) ≤ ((2226852649583 / 288230376151711744 : ℚ) : ℝ) := by
  have h : ((142518569573309 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((637 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-479 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((637 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-479 / 48 : ℚ) : ℝ) ≤ ((2226852649583 / 288230376151711744 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2548 : ((142076249 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((637 / 16 : ℚ) : ℝ) ∧
    logKernel ((637 / 16 : ℚ) : ℝ) ≤ ((568305001 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2548
  constructor
  · exact (show ((142076249 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((142518569573309 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((637 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((2226852649583 / 288230376151711744 : ℚ) : ℝ) ≤ ((568305001 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2549 : ((70154511976015 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2549 / 64 : ℚ) : ℝ) ∧
    heightZ ((2549 / 64 : ℚ) : ℝ) ≤ ((140309023952033 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((70154511976015 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2549 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1919 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2549 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1919 / 192 : ℚ) : ℝ) ≤ ((140309023952033 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2549 : ((550820089 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2549 / 64 : ℚ) : ℝ) ∧
    logKernel ((2549 / 64 : ℚ) : ℝ) ≤ ((275410047 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2549
  constructor
  · exact (show ((550820089 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((70154511976015 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2549 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((140309023952033 / 18446744073709551616 : ℚ) : ℝ) ≤ ((275410047 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2550 : ((4316679192515 / 576460752303423488 : ℚ) : ℝ) ≤ heightZ ((1275 / 32 : ℚ) : ℝ) ∧
    heightZ ((1275 / 32 : ℚ) : ℝ) ≤ ((138133734160483 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((4316679192515 / 576460752303423488 : ℚ) : ℝ) ≤ Real.exp (-((1275 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-961 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1275 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-961 / 96 : ℚ) : ℝ) ≤ ((138133734160483 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2550 : ((533873137 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1275 / 32 : ℚ) : ℝ) ∧
    logKernel ((1275 / 32 : ℚ) : ℝ) ≤ ((266936571 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2550
  constructor
  · exact (show ((533873137 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((4316679192515 / 576460752303423488 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1275 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((138133734160483 / 18446744073709551616 : ℚ) : ℝ) ≤ ((266936571 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2551 : ((135992169111245 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2551 / 64 : ℚ) : ℝ) ∧
    heightZ ((2551 / 64 : ℚ) : ℝ) ≤ ((8499510569453 / 1152921504606846976 : ℚ) : ℝ) := by
  have h : ((135992169111245 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2551 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1925 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2551 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1925 / 192 : ℚ) : ℝ) ≤ ((8499510569453 / 1152921504606846976 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2551 : ((517447587 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2551 / 64 : ℚ) : ℝ) ∧
    logKernel ((2551 / 64 : ℚ) : ℝ) ≤ ((64680949 / 9007199254740992 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2551
  constructor
  · exact (show ((517447587 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((135992169111245 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2551 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((8499510569453 / 1152921504606846976 : ℚ) : ℝ) ≤ ((64680949 / 9007199254740992 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2552 : ((66941902975329 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((319 / 8 : ℚ) : ℝ) ∧
    heightZ ((319 / 8 : ℚ) : ℝ) ≤ ((133883805950661 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((66941902975329 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((319 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-241 / 24 : ℚ) : ℝ) ∧
      Real.exp (-((319 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-241 / 24 : ℚ) : ℝ) ≤ ((133883805950661 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2552 : ((250763699 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((319 / 8 : ℚ) : ℝ) ∧
    logKernel ((319 / 8 : ℚ) : ℝ) ≤ ((501527403 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2552
  constructor
  · exact (show ((250763699 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((66941902975329 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((319 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((133883805950661 / 18446744073709551616 : ℚ) : ℝ) ≤ ((501527403 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2553 : ((65904064965573 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2553 / 64 : ℚ) : ℝ) ∧
    heightZ ((2553 / 64 : ℚ) : ℝ) ≤ ((131808129931149 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((65904064965573 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2553 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1931 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2553 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1931 / 192 : ℚ) : ℝ) ≤ ((131808129931149 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2553 : ((243048511 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2553 / 64 : ℚ) : ℝ) ∧
    logKernel ((2553 / 64 : ℚ) : ℝ) ≤ ((486097027 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2553
  constructor
  · exact (show ((243048511 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((65904064965573 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2553 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((131808129931149 / 18446744073709551616 : ℚ) : ℝ) ≤ ((486097027 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2554 : ((129764634285559 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1277 / 32 : ℚ) : ℝ) ∧
    heightZ ((1277 / 32 : ℚ) : ℝ) ≤ ((64882317142781 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((129764634285559 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1277 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-967 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1277 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-967 / 96 : ℚ) : ℝ) ≤ ((64882317142781 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2554 : ((471141389 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1277 / 32 : ℚ) : ℝ) ∧
    logKernel ((1277 / 32 : ℚ) : ℝ) ≤ ((235570697 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2554
  constructor
  · exact (show ((471141389 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((129764634285559 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1277 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((64882317142781 / 9223372036854775808 : ℚ) : ℝ) ≤ ((235570697 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2555 : ((127752820103443 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2555 / 64 : ℚ) : ℝ) ∧
    heightZ ((2555 / 64 : ℚ) : ℝ) ≤ ((63876410051723 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((127752820103443 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2555 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1937 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2555 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1937 / 192 : ℚ) : ℝ) ≤ ((63876410051723 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2555 : ((456645893 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2555 / 64 : ℚ) : ℝ) ∧
    logKernel ((2555 / 64 : ℚ) : ℝ) ≤ ((228322949 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2555
  constructor
  · exact (show ((456645893 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((127752820103443 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2555 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((63876410051723 / 9223372036854775808 : ℚ) : ℝ) ≤ ((228322949 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2556 : ((7860762263077 / 1152921504606846976 : ℚ) : ℝ) ≤ heightZ ((639 / 16 : ℚ) : ℝ) ∧
    heightZ ((639 / 16 : ℚ) : ℝ) ≤ ((125772196209235 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((7860762263077 / 1152921504606846976 : ℚ) : ℝ) ≤ Real.exp (-((639 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-485 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((639 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-485 / 48 : ℚ) : ℝ) ≤ ((125772196209235 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2556 : ((442596375 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((639 / 16 : ℚ) : ℝ) ∧
    logKernel ((639 / 16 : ℚ) : ℝ) ≤ ((110649095 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2556
  constructor
  · exact (show ((442596375 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((7860762263077 / 1152921504606846976 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((639 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((125772196209235 / 18446744073709551616 : ℚ) : ℝ) ≤ ((110649095 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2557 : ((61911139521167 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2557 / 64 : ℚ) : ℝ) ∧
    heightZ ((2557 / 64 : ℚ) : ℝ) ≤ ((123822279042337 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((61911139521167 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2557 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1943 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2557 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1943 / 192 : ℚ) : ℝ) ≤ ((123822279042337 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2557 : ((107244779 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((2557 / 64 : ℚ) : ℝ) ∧
    logKernel ((2557 / 64 : ℚ) : ℝ) ≤ ((428979121 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2557
  constructor
  · exact (show ((107244779 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((61911139521167 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2557 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((123822279042337 / 18446744073709551616 : ℚ) : ℝ) ≤ ((428979121 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2558 : ((30475648134767 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((1279 / 32 : ℚ) : ℝ) ∧
    heightZ ((1279 / 32 : ℚ) : ℝ) ≤ ((121902592539071 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((30475648134767 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((1279 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-973 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1279 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-973 / 96 : ℚ) : ℝ) ≤ ((121902592539071 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2558 : ((25986301 / 4503599627370496 : ℚ) : ℝ) ≤ logKernel ((1279 / 32 : ℚ) : ℝ) ∧
    logKernel ((1279 / 32 : ℚ) : ℝ) ≤ ((415780821 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2558
  constructor
  · exact (show ((25986301 / 4503599627370496 : ℚ) : ℝ) ≤ zKernel ((30475648134767 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1279 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((121902592539071 / 18446744073709551616 : ℚ) : ℝ) ≤ ((415780821 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2559 : ((60006334008217 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2559 / 64 : ℚ) : ℝ) ∧
    heightZ ((2559 / 64 : ℚ) : ℝ) ≤ ((120012668016437 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((60006334008217 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2559 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1949 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2559 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1949 / 192 : ℚ) : ℝ) ≤ ((120012668016437 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2559 : ((402988585 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2559 / 64 : ℚ) : ℝ) ∧
    logKernel ((2559 / 64 : ℚ) : ℝ) ≤ ((201494295 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2559
  constructor
  · exact (show ((402988585 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((60006334008217 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2559 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((120012668016437 / 18446744073709551616 : ℚ) : ℝ) ≤ ((201494295 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2560 : ((29538011014423 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((40 / 1 : ℚ) : ℝ) ∧
    heightZ ((40 / 1 : ℚ) : ℝ) ≤ ((118152044057695 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((29538011014423 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((40 / 1 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-61 / 6 : ℚ) : ℝ) ∧
      Real.exp (-((40 / 1 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-61 / 6 : ℚ) : ℝ) ≤ ((118152044057695 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2560 : ((195294965 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((40 / 1 : ℚ) : ℝ) ∧
    logKernel ((40 / 1 : ℚ) : ℝ) ≤ ((390589935 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2560
  constructor
  · exact (show ((195294965 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((29538011014423 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((40 / 1 : ℚ) : ℝ)) hh).trans
      (show zKernel ((118152044057695 / 18446744073709551616 : ℚ) : ℝ) ≤ ((390589935 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2561 : ((14540033299963 / 2305843009213693952 : ℚ) : ℝ) ≤ heightZ ((2561 / 64 : ℚ) : ℝ) ∧
    heightZ ((2561 / 64 : ℚ) : ℝ) ≤ ((116320266399707 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((14540033299963 / 2305843009213693952 : ℚ) : ℝ) ≤ Real.exp (-((2561 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1955 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2561 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1955 / 192 : ℚ) : ℝ) ≤ ((116320266399707 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2561 : ((378572741 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2561 / 64 : ℚ) : ℝ) ∧
    logKernel ((2561 / 64 : ℚ) : ℝ) ≤ ((189286373 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2561
  constructor
  · exact (show ((378572741 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((14540033299963 / 2305843009213693952 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2561 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((116320266399707 / 18446744073709551616 : ℚ) : ℝ) ≤ ((189286373 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2562 : ((114516887822029 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1281 / 32 : ℚ) : ℝ) ∧
    heightZ ((1281 / 32 : ℚ) : ℝ) ≤ ((7157305488877 / 1152921504606846976 : ℚ) : ℝ) := by
  have h : ((114516887822029 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1281 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-979 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1281 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-979 / 96 : ℚ) : ℝ) ≤ ((7157305488877 / 1152921504606846976 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2562 : ((183462641 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((1281 / 32 : ℚ) : ℝ) ∧
    logKernel ((1281 / 32 : ℚ) : ℝ) ≤ ((366925287 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2562
  constructor
  · exact (show ((183462641 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((114516887822029 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1281 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((7157305488877 / 1152921504606846976 : ℚ) : ℝ) ≤ ((366925287 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2563 : ((112741468037735 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2563 / 64 : ℚ) : ℝ) ∧
    heightZ ((2563 / 64 : ℚ) : ℝ) ≤ ((56370734018869 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((112741468037735 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2563 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1961 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2563 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1961 / 192 : ℚ) : ℝ) ≤ ((56370734018869 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2563 : ((177818089 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2563 / 64 : ℚ) : ℝ) ∧
    logKernel ((2563 / 64 : ℚ) : ℝ) ≤ ((355636183 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2563
  constructor
  · exact (show ((177818089 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((112741468037735 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2563 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((56370734018869 / 9223372036854775808 : ℚ) : ℝ) ≤ ((355636183 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2564 : ((110993573585909 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((641 / 16 : ℚ) : ℝ) ∧
    heightZ ((641 / 16 : ℚ) : ℝ) ≤ ((13874196698239 / 2305843009213693952 : ℚ) : ℝ) := by
  have h : ((110993573585909 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((641 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-491 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((641 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-491 / 48 : ℚ) : ℝ) ≤ ((13874196698239 / 2305843009213693952 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2564 : ((344694403 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((641 / 16 : ℚ) : ℝ) ∧
    logKernel ((641 / 16 : ℚ) : ℝ) ≤ ((43086801 / 9007199254740992 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2564
  constructor
  · exact (show ((344694403 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((110993573585909 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((641 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((13874196698239 / 2305843009213693952 : ℚ) : ℝ) ≤ ((43086801 / 9007199254740992 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2565 : ((109272777725825 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2565 / 64 : ℚ) : ℝ) ∧
    heightZ ((2565 / 64 : ℚ) : ℝ) ≤ ((27318194431457 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((109272777725825 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2565 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1967 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2565 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1967 / 192 : ℚ) : ℝ) ≤ ((27318194431457 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2565 : ((334089271 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2565 / 64 : ℚ) : ℝ) ∧
    logKernel ((2565 / 64 : ℚ) : ℝ) ≤ ((83522319 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2565
  constructor
  · exact (show ((334089271 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((109272777725825 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2565 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((27318194431457 / 4611686018427387904 : ℚ) : ℝ) ≤ ((83522319 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2566 : ((107578660332759 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1283 / 32 : ℚ) : ℝ) ∧
    heightZ ((1283 / 32 : ℚ) : ℝ) ≤ ((53789330166381 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((107578660332759 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1283 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-985 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1283 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-985 / 96 : ℚ) : ℝ) ≤ ((53789330166381 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2566 : ((323810425 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1283 / 32 : ℚ) : ℝ) ∧
    logKernel ((1283 / 32 : ℚ) : ℝ) ≤ ((161905215 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2566
  constructor
  · exact (show ((323810425 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((107578660332759 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1283 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((53789330166381 / 9223372036854775808 : ℚ) : ℝ) ≤ ((161905215 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2567 : ((13238850974427 / 2305843009213693952 : ℚ) : ℝ) ≤ heightZ ((2567 / 64 : ℚ) : ℝ) ∧
    heightZ ((2567 / 64 : ℚ) : ℝ) ≤ ((105910807795419 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((13238850974427 / 2305843009213693952 : ℚ) : ℝ) ≤ Real.exp (-((2567 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1973 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2567 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1973 / 192 : ℚ) : ℝ) ≤ ((105910807795419 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2567 : ((313847825 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2567 / 64 : ℚ) : ℝ) ∧
    logKernel ((2567 / 64 : ℚ) : ℝ) ≤ ((156923915 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2567
  constructor
  · exact (show ((313847825 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((13238850974427 / 2305843009213693952 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2567 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((105910807795419 / 18446744073709551616 : ℚ) : ℝ) ≤ ((156923915 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2568 : ((13033601614369 / 2305843009213693952 : ℚ) : ℝ) ≤ heightZ ((321 / 8 : ℚ) : ℝ) ∧
    heightZ ((321 / 8 : ℚ) : ℝ) ≤ ((104268812914955 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((13033601614369 / 2305843009213693952 : ℚ) : ℝ) ≤ Real.exp (-((321 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-247 / 24 : ℚ) : ℝ) ∧
      Real.exp (-((321 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-247 / 24 : ℚ) : ℝ) ≤ ((104268812914955 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2568 : ((304191743 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((321 / 8 : ℚ) : ℝ) ∧
    logKernel ((321 / 8 : ℚ) : ℝ) ≤ ((76047937 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2568
  constructor
  · exact (show ((304191743 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((13033601614369 / 2305843009213693952 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((321 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((104268812914955 / 18446744073709551616 : ℚ) : ℝ) ≤ ((76047937 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2569 : ((51326137402777 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2569 / 64 : ℚ) : ℝ) ∧
    heightZ ((2569 / 64 : ℚ) : ℝ) ≤ ((102652274805557 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((51326137402777 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2569 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1979 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2569 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1979 / 192 : ℚ) : ℝ) ≤ ((102652274805557 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2569 : ((294832747 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2569 / 64 : ℚ) : ℝ) ∧
    logKernel ((2569 / 64 : ℚ) : ℝ) ≤ ((18427047 / 4503599627370496 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2569
  constructor
  · exact (show ((294832747 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((51326137402777 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2569 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((102652274805557 / 18446744073709551616 : ℚ) : ℝ) ≤ ((18427047 / 4503599627370496 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2570 : ((12632599849571 / 2305843009213693952 : ℚ) : ℝ) ≤ heightZ ((1285 / 32 : ℚ) : ℝ) ∧
    heightZ ((1285 / 32 : ℚ) : ℝ) ≤ ((101060798796571 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((12632599849571 / 2305843009213693952 : ℚ) : ℝ) ≤ Real.exp (-((1285 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-991 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1285 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-991 / 96 : ℚ) : ℝ) ≤ ((101060798796571 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2570 : ((285761697 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1285 / 32 : ℚ) : ℝ) ∧
    logKernel ((1285 / 32 : ℚ) : ℝ) ≤ ((142880851 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2570
  constructor
  · exact (show ((285761697 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((12632599849571 / 2305843009213693952 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1285 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((101060798796571 / 18446744073709551616 : ℚ) : ℝ) ≤ ((142880851 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2571 : ((99493996336141 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2571 / 64 : ℚ) : ℝ) ∧
    heightZ ((2571 / 64 : ℚ) : ℝ) ≤ ((6218374771009 / 1152921504606846976 : ℚ) : ℝ) := by
  have h : ((99493996336141 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2571 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1985 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2571 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1985 / 192 : ℚ) : ℝ) ≤ ((6218374771009 / 1152921504606846976 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2571 : ((276969733 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2571 / 64 : ℚ) : ℝ) ∧
    logKernel ((2571 / 64 : ℚ) : ℝ) ≤ ((138484869 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2571
  constructor
  · exact (show ((276969733 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((99493996336141 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2571 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((6218374771009 / 1152921504606846976 : ℚ) : ℝ) ≤ ((138484869 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2572 : ((12243935612045 / 2305843009213693952 : ℚ) : ℝ) ≤ heightZ ((643 / 16 : ℚ) : ℝ) ∧
    heightZ ((643 / 16 : ℚ) : ℝ) ≤ ((97951484896363 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((12243935612045 / 2305843009213693952 : ℚ) : ℝ) ≤ Real.exp (-((643 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-497 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((643 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-497 / 48 : ℚ) : ℝ) ≤ ((97951484896363 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2572 : ((268448271 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((643 / 16 : ℚ) : ℝ) ∧
    logKernel ((643 / 16 : ℚ) : ℝ) ≤ ((67112069 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2572
  constructor
  · exact (show ((268448271 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((12243935612045 / 2305843009213693952 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((643 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((97951484896363 / 18446744073709551616 : ℚ) : ℝ) ≤ ((67112069 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2573 : ((6027055492491 / 1152921504606846976 : ℚ) : ℝ) ≤ heightZ ((2573 / 64 : ℚ) : ℝ) ∧
    heightZ ((2573 / 64 : ℚ) : ℝ) ≤ ((96432887879859 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((6027055492491 / 1152921504606846976 : ℚ) : ℝ) ≤ Real.exp (-((2573 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1991 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2573 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1991 / 192 : ℚ) : ℝ) ≤ ((96432887879859 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2573 : ((260188985 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2573 / 64 : ℚ) : ℝ) ∧
    logKernel ((2573 / 64 : ℚ) : ℝ) ≤ ((130094495 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2573
  constructor
  · exact (show ((260188985 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((6027055492491 / 1152921504606846976 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2573 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((96432887879859 / 18446744073709551616 : ℚ) : ℝ) ≤ ((130094495 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2574 : ((23734458631965 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((1287 / 32 : ℚ) : ℝ) ∧
    heightZ ((1287 / 32 : ℚ) : ℝ) ≤ ((94937834527863 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((23734458631965 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((1287 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-997 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1287 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-997 / 96 : ℚ) : ℝ) ≤ ((94937834527863 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2574 : ((63045953 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((1287 / 32 : ℚ) : ℝ) ∧
    logKernel ((1287 / 32 : ℚ) : ℝ) ≤ ((252183817 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2574
  constructor
  · exact (show ((63045953 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((23734458631965 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1287 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((94937834527863 / 18446744073709551616 : ℚ) : ℝ) ≤ ((252183817 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2575 : ((93465959829687 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2575 / 64 : ℚ) : ℝ) ∧
    heightZ ((2575 / 64 : ℚ) : ℝ) ≤ ((46732979914845 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((93465959829687 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2575 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1997 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2575 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1997 / 192 : ℚ) : ℝ) ≤ ((46732979914845 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2575 : ((61106233 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((2575 / 64 : ℚ) : ℝ) ∧
    logKernel ((2575 / 64 : ℚ) : ℝ) ≤ ((244424937 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2575
  constructor
  · exact (show ((61106233 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((93465959829687 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2575 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((46732979914845 / 9223372036854775808 : ℚ) : ℝ) ≤ ((244424937 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2576 : ((46008452216809 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((161 / 4 : ℚ) : ℝ) ∧
    heightZ ((161 / 4 : ℚ) : ℝ) ≤ ((92016904433621 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((46008452216809 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((161 / 4 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-125 / 12 : ℚ) : ℝ) ∧
      Real.exp (-((161 / 4 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-125 / 12 : ℚ) : ℝ) ≤ ((92016904433621 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2576 : ((236904767 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((161 / 4 : ℚ) : ℝ) ∧
    logKernel ((161 / 4 : ℚ) : ℝ) ≤ ((59226193 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2576
  constructor
  · exact (show ((236904767 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((46008452216809 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((161 / 4 : ℚ) : ℝ)) hh).trans
      (show zKernel ((92016904433621 / 18446744073709551616 : ℚ) : ℝ) ≤ ((59226193 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2577 : ((22647578639791 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((2577 / 64 : ℚ) : ℝ) ∧
    heightZ ((2577 / 64 : ℚ) : ℝ) ≤ ((90590314559167 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((22647578639791 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((2577 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2003 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2577 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2003 / 192 : ℚ) : ℝ) ≤ ((90590314559167 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2577 : ((229615973 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2577 / 64 : ℚ) : ℝ) ∧
    logKernel ((2577 / 64 : ℚ) : ℝ) ≤ ((114807989 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2577
  constructor
  · exact (show ((229615973 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((22647578639791 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2577 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((90590314559167 / 18446744073709551616 : ℚ) : ℝ) ≤ ((114807989 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem log_height_bounds_704 : ((265416631725958021 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1273 / 32 : ℚ) : ℝ) ∧
    Real.log ((1273 / 32 : ℚ) : ℝ) ≤ ((33177078965744753 / 9007199254740992 : ℚ) : ℝ) := by
  have hl : Real.exp ((265416631725958021 / 72057594037927936 : ℚ) : ℝ) ≤ ((1273 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1273 / 32 : ℚ) : ℝ) ≤ Real.exp ((33177078965744753 / 9007199254740992 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_704 : heightPower (704 : Fin 988) ≤ ((3187428461609381 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_704
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_704 : heightFactor (704 : Fin 988) ≤ ((5173899179 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_704
  obtain ⟨hpl, hph⟩ := kernel_bounds_2545
  obtain ⟨hcl, hch⟩ := kernel_bounds_2546
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2546
  have h : (((1620529 / 512 : ℚ) : ℝ) * (logKernel ((2545 / 64 : ℚ) : ℝ) - logKernel ((1273 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1273 / 32 : ℚ) : ℝ) + Real.log ((1273 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((5173899179 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_705 : ((132722464222484985 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2547 / 64 : ℚ) : ℝ) ∧
    Real.log ((2547 / 64 : ℚ) : ℝ) ≤ ((265444928444969973 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((132722464222484985 / 36028797018963968 : ℚ) : ℝ) ≤ ((2547 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2547 / 64 : ℚ) : ℝ) ≤ Real.exp ((265444928444969973 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_705 : heightPower (705 : Fin 988) ≤ ((3191937042179125 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_705
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_705 : heightFactor (705 : Fin 988) ≤ ((10091046675 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_705
  obtain ⟨hpl, hph⟩ := kernel_bounds_2546
  obtain ⟨hcl, hch⟩ := kernel_bounds_2547
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2547
  have h : (((6487209 / 2048 : ℚ) : ℝ) * (logKernel ((1273 / 32 : ℚ) : ℝ) - logKernel ((2547 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2547 / 64 : ℚ) : ℝ) + Real.log ((2547 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((10091046675 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_706 : ((132736607028169617 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((637 / 16 : ℚ) : ℝ) ∧
    Real.log ((637 / 16 : ℚ) : ℝ) ≤ ((265473214056339237 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((132736607028169617 / 36028797018963968 : ℚ) : ℝ) ≤ ((637 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((637 / 16 : ℚ) : ℝ) ≤ Real.exp ((265473214056339237 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_706 : heightPower (706 : Fin 988) ≤ ((3196445579359641 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_706
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_706 : heightFactor (706 : Fin 988) ≤ ((2460165517 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_706
  obtain ⟨hpl, hph⟩ := kernel_bounds_2547
  obtain ⟨hcl, hch⟩ := kernel_bounds_2548
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2548
  have h : (((405769 / 128 : ℚ) : ℝ) * (logKernel ((2547 / 64 : ℚ) : ℝ) - logKernel ((637 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((637 / 16 : ℚ) : ℝ) + Real.log ((637 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((2460165517 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_707 : ((265501488568782819 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2549 / 64 : ℚ) : ℝ) ∧
    Real.log ((2549 / 64 : ℚ) : ℝ) ≤ ((132750744284391411 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((265501488568782819 / 72057594037927936 : ℚ) : ℝ) ≤ ((2549 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2549 / 64 : ℚ) : ℝ) ≤ Real.exp ((132750744284391411 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_707 : heightPower (707 : Fin 988) ≤ ((3200954073184977 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_707
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_707 : heightFactor (707 : Fin 988) ≤ ((9596486733 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_707
  obtain ⟨hpl, hph⟩ := kernel_bounds_2548
  obtain ⟨hcl, hch⟩ := kernel_bounds_2549
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2549
  have h : (((6497401 / 2048 : ℚ) : ℝ) * (logKernel ((637 / 16 : ℚ) : ℝ) - logKernel ((2549 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2549 / 64 : ℚ) : ℝ) + Real.log ((2549 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((9596486733 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_708 : ((265529751991007471 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1275 / 32 : ℚ) : ℝ) ∧
    Real.log ((1275 / 32 : ℚ) : ℝ) ≤ ((132764875995503737 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((265529751991007471 / 72057594037927936 : ℚ) : ℝ) ≤ ((1275 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1275 / 32 : ℚ) : ℝ) ≤ Real.exp ((132764875995503737 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_708 : heightPower (708 : Fin 988) ≤ ((1602731261844573 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_708
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_708 : heightFactor (708 : Fin 988) ≤ ((9358366775 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_708
  obtain ⟨hpl, hph⟩ := kernel_bounds_2549
  obtain ⟨hcl, hch⟩ := kernel_bounds_2550
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2550
  have h : (((1625625 / 512 : ℚ) : ℝ) * (logKernel ((2549 / 64 : ℚ) : ℝ) - logKernel ((1275 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1275 / 32 : ℚ) : ℝ) + Real.log ((1275 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((9358366775 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_709 : ((1037335954420741 / 281474976710656 : ℚ) : ℝ) ≤ Real.log ((2551 / 64 : ℚ) : ℝ) ∧
    Real.log ((2551 / 64 : ℚ) : ℝ) ≤ ((265558004331709699 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((1037335954420741 / 281474976710656 : ℚ) : ℝ) ≤ ((2551 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2551 / 64 : ℚ) : ℝ) ≤ Real.exp ((265558004331709699 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_709 : heightPower (709 : Fin 988) ≤ ((3209970930906119 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_709
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_709 : heightFactor (709 : Fin 988) ≤ ((9126152111 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_709
  obtain ⟨hpl, hph⟩ := kernel_bounds_2550
  obtain ⟨hcl, hch⟩ := kernel_bounds_2551
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2551
  have h : (((6507601 / 2048 : ℚ) : ℝ) * (logKernel ((1275 / 32 : ℚ) : ℝ) - logKernel ((2551 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2551 / 64 : ℚ) : ℝ) + Real.log ((2551 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((9126152111 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_710 : ((8299570174986743 / 2251799813685248 : ℚ) : ℝ) ≤ Real.log ((319 / 8 : ℚ) : ℝ) ∧
    Real.log ((319 / 8 : ℚ) : ℝ) ≤ ((265586245599575779 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((8299570174986743 / 2251799813685248 : ℚ) : ℝ) ≤ ((319 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((319 / 8 : ℚ) : ℝ) ≤ Real.exp ((265586245599575779 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_710 : heightPower (710 : Fin 988) ≤ ((50226238982341 / 4398046511104 : ℚ) : ℝ) := by
  have hh := log_height_bounds_710
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_710 : heightFactor (710 : Fin 988) ≤ ((1112462047 / 35184372088832 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_710
  obtain ⟨hpl, hph⟩ := kernel_bounds_2551
  obtain ⟨hcl, hch⟩ := kernel_bounds_2552
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2552
  have h : (((101761 / 32 : ℚ) : ℝ) * (logKernel ((2551 / 64 : ℚ) : ℝ) - logKernel ((319 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((319 / 8 : ℚ) : ℝ) + Real.log ((319 / 8 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1112462047 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_711 : ((132807237901640891 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2553 / 64 : ℚ) : ℝ) ∧
    Real.log ((2553 / 64 : ℚ) : ℝ) ≤ ((265614475803281785 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((132807237901640891 / 36028797018963968 : ℚ) : ℝ) ≤ ((2553 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2553 / 64 : ℚ) : ℝ) ≤ Real.exp ((265614475803281785 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_711 : heightPower (711 : Fin 988) ≤ ((3218987615614155 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_711
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_711 : heightFactor (711 : Fin 988) ≤ ((8678856829 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_711
  obtain ⟨hpl, hph⟩ := kernel_bounds_2552
  obtain ⟨hcl, hch⟩ := kernel_bounds_2553
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2553
  have h : (((6517809 / 2048 : ℚ) : ℝ) * (logKernel ((319 / 8 : ℚ) : ℝ) - logKernel ((2553 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2553 / 64 : ℚ) : ℝ) + Real.log ((2553 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((8678856829 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_712 : ((265642694951493593 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1277 / 32 : ℚ) : ℝ) ∧
    Real.log ((1277 / 32 : ℚ) : ℝ) ≤ ((66410673737873399 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((265642694951493593 / 72057594037927936 : ℚ) : ℝ) ≤ ((1277 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1277 / 32 : ℚ) : ℝ) ≤ Real.exp ((66410673737873399 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_712 : heightPower (712 : Fin 988) ≤ ((3223495893172961 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_712
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_712 : heightFactor (712 : Fin 988) ≤ ((8463494267 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_712
  obtain ⟨hpl, hph⟩ := kernel_bounds_2553
  obtain ⟨hcl, hch⟩ := kernel_bounds_2554
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2554
  have h : (((1630729 / 512 : ℚ) : ℝ) * (logKernel ((2553 / 64 : ℚ) : ℝ) - logKernel ((1277 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1277 / 32 : ℚ) : ℝ) + Real.log ((1277 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((8463494267 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_713 : ((265670903052866909 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2555 / 64 : ℚ) : ℝ) ∧
    Real.log ((2555 / 64 : ℚ) : ℝ) ≤ ((8302215720402091 / 2251799813685248 : ℚ) : ℝ) := by
  have hl : Real.exp ((265670903052866909 / 72057594037927936 : ℚ) : ℝ) ≤ ((2555 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2555 / 64 : ℚ) : ℝ) ≤ Real.exp ((8302215720402091 / 2251799813685248 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_713 : heightPower (713 : Fin 988) ≤ ((3228004127580055 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_713
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_713 : heightFactor (713 : Fin 988) ≤ ((8253472933 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_713
  obtain ⟨hpl, hph⟩ := kernel_bounds_2554
  obtain ⟨hcl, hch⟩ := kernel_bounds_2555
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2555
  have h : (((6528025 / 2048 : ℚ) : ℝ) * (logKernel ((1277 / 32 : ℚ) : ℝ) - logKernel ((2555 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2555 / 64 : ℚ) : ℝ) + Real.log ((2555 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((8253472933 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_714 : ((33212387514505909 / 9007199254740992 : ℚ) : ℝ) ≤ Real.log ((639 / 16 : ℚ) : ℝ) ∧
    Real.log ((639 / 16 : ℚ) : ℝ) ≤ ((265699100116047275 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((33212387514505909 / 9007199254740992 : ℚ) : ℝ) ≤ ((639 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((639 / 16 : ℚ) : ℝ) ≤ Real.exp ((265699100116047275 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_714 : heightPower (714 : Fin 988) ≤ ((3232512318869207 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_714
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_714 : heightFactor (714 : Fin 988) ≤ ((2012165109 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_714
  obtain ⟨hpl, hph⟩ := kernel_bounds_2555
  obtain ⟨hcl, hch⟩ := kernel_bounds_2556
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2556
  have h : (((408321 / 128 : ℚ) : ℝ) * (logKernel ((2555 / 64 : ℚ) : ℝ) - logKernel ((639 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((639 / 16 : ℚ) : ℝ) + Real.log ((639 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((2012165109 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_715 : ((66431821537417519 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((2557 / 64 : ℚ) : ℝ) ∧
    Real.log ((2557 / 64 : ℚ) : ℝ) ≤ ((265727286149670079 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((66431821537417519 / 18014398509481984 : ℚ) : ℝ) ≤ ((2557 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2557 / 64 : ℚ) : ℝ) ≤ Real.exp ((265727286149670079 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_715 : heightPower (715 : Fin 988) ≤ ((1618510233537075 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_715
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_715 : heightFactor (715 : Fin 988) ≤ ((3924463831 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_715
  obtain ⟨hpl, hph⟩ := kernel_bounds_2556
  obtain ⟨hcl, hch⟩ := kernel_bounds_2557
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2557
  have h : (((6538249 / 2048 : ℚ) : ℝ) * (logKernel ((639 / 16 : ℚ) : ℝ) - logKernel ((2557 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2557 / 64 : ℚ) : ℝ) + Real.log ((2557 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((3924463831 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_716 : ((132877730581180293 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((1279 / 32 : ℚ) : ℝ) ∧
    Real.log ((1279 / 32 : ℚ) : ℝ) ≤ ((265755461162360589 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((132877730581180293 / 36028797018963968 : ℚ) : ℝ) ≤ ((1279 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1279 / 32 : ℚ) : ℝ) ≤ Real.exp ((265755461162360589 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_716 : heightPower (716 : Fin 988) ≤ ((3241528572228577 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_716
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_716 : heightFactor (716 : Fin 988) ≤ ((956768587 / 35184372088832 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_716
  obtain ⟨hpl, hph⟩ := kernel_bounds_2557
  obtain ⟨hcl, hch⟩ := kernel_bounds_2558
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2558
  have h : (((1635841 / 512 : ℚ) : ℝ) * (logKernel ((2557 / 64 : ℚ) : ℝ) - logKernel ((1279 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1279 / 32 : ℚ) : ℝ) + Real.log ((1279 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((956768587 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_717 : ((132891812581366977 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2559 / 64 : ℚ) : ℝ) ∧
    Real.log ((2559 / 64 : ℚ) : ℝ) ≤ ((265783625162733957 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((132891812581366977 / 36028797018963968 : ℚ) : ℝ) ≤ ((2559 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2559 / 64 : ℚ) : ℝ) ≤ Real.exp ((265783625162733957 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_717 : heightPower (717 : Fin 988) ≤ ((3246036634366139 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_717
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_717 : heightFactor (717 : Fin 988) ≤ ((3732100371 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_717
  obtain ⟨hpl, hph⟩ := kernel_bounds_2558
  obtain ⟨hcl, hch⟩ := kernel_bounds_2559
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2559
  have h : (((6548481 / 2048 : ℚ) : ℝ) * (logKernel ((1279 / 32 : ℚ) : ℝ) - logKernel ((2559 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2559 / 64 : ℚ) : ℝ) + Real.log ((2559 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((3732100371 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_718 : ((132905889079697617 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((40 / 1 : ℚ) : ℝ) ∧
    Real.log ((40 / 1 : ℚ) : ℝ) ≤ ((265811778159395237 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((132905889079697617 / 36028797018963968 : ℚ) : ℝ) ≤ ((40 / 1 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((40 / 1 : ℚ) : ℝ) ≤ Real.exp ((265811778159395237 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_718 : heightPower (718 : Fin 988) ≤ ((3250544653520451 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_718
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_718 : heightFactor (718 : Fin 988) ≤ ((7278964049 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_718
  obtain ⟨hpl, hph⟩ := kernel_bounds_2559
  obtain ⟨hcl, hch⟩ := kernel_bounds_2560
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2560
  have h : (((3200 / 1 : ℚ) : ℝ) * (logKernel ((2559 / 64 : ℚ) : ℝ) - logKernel ((40 / 1 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((40 / 1 : ℚ) : ℝ) + Real.log ((40 / 1 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((7278964049 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_719 : ((265839920160939397 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2561 / 64 : ℚ) : ℝ) ∧
    Real.log ((2561 / 64 : ℚ) : ℝ) ≤ ((33229990020117425 / 9007199254740992 : ℚ) : ℝ) := by
  have hl : Real.exp ((265839920160939397 / 72057594037927936 : ℚ) : ℝ) ≤ ((2561 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2561 / 64 : ℚ) : ℝ) ≤ Real.exp ((33229990020117425 / 9007199254740992 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_719 : heightPower (719 : Fin 988) ≤ ((3255052629725087 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_719
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_719 : heightFactor (719 : Fin 988) ≤ ((1774580457 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_719
  obtain ⟨hpl, hph⟩ := kernel_bounds_2560
  obtain ⟨hcl, hch⟩ := kernel_bounds_2561
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2561
  have h : (((6558721 / 2048 : ℚ) : ℝ) * (logKernel ((40 / 1 : ℚ) : ℝ) - logKernel ((2561 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2561 / 64 : ℚ) : ℝ) + Real.log ((2561 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1774580457 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_720 : ((265868051175951349 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1281 / 32 : ℚ) : ℝ) ∧
    Real.log ((1281 / 32 : ℚ) : ℝ) ≤ ((33233506396993919 / 9007199254740992 : ℚ) : ℝ) := by
  have hl : Real.exp ((265868051175951349 / 72057594037927936 : ℚ) : ℝ) ≤ ((1281 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1281 / 32 : ℚ) : ℝ) ≤ Real.exp ((33233506396993919 / 9007199254740992 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_720 : heightPower (720 : Fin 988) ≤ ((3259560563013581 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_720
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_720 : heightFactor (720 : Fin 988) ≤ ((1730540047 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_720
  obtain ⟨hpl, hph⟩ := kernel_bounds_2561
  obtain ⟨hcl, hch⟩ := kernel_bounds_2562
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2562
  have h : (((1640961 / 512 : ℚ) : ℝ) * (logKernel ((2561 / 64 : ℚ) : ℝ) - logKernel ((1281 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1281 / 32 : ℚ) : ℝ) + Real.log ((1281 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1730540047 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_721 : ((265896171213005945 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2563 / 64 : ℚ) : ℝ) ∧
    Real.log ((2563 / 64 : ℚ) : ℝ) ≤ ((66474042803251487 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((265896171213005945 / 72057594037927936 : ℚ) : ℝ) ≤ ((2563 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2563 / 64 : ℚ) : ℝ) ≤ Real.exp ((66474042803251487 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_721 : heightPower (721 : Fin 988) ≤ ((1632034226709715 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_721
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_721 : heightFactor (721 : Fin 988) ≤ ((843796007 / 35184372088832 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_721
  obtain ⟨hpl, hph⟩ := kernel_bounds_2562
  obtain ⟨hcl, hch⟩ := kernel_bounds_2563
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2563
  have h : (((6568969 / 2048 : ℚ) : ℝ) * (logKernel ((1281 / 32 : ℚ) : ℝ) - logKernel ((2563 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2563 / 64 : ℚ) : ℝ) + Real.log ((2563 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((843796007 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_722 : ((265924280280668003 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((641 / 16 : ℚ) : ℝ) ∧
    Real.log ((641 / 16 : ℚ) : ℝ) ≤ ((132962140140334003 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((265924280280668003 / 72057594037927936 : ℚ) : ℝ) ≤ ((641 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((641 / 16 : ℚ) : ℝ) ≤ Real.exp ((132962140140334003 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_722 : heightPower (722 : Fin 988) ≤ ((3268576300976089 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_722
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_722 : heightFactor (722 : Fin 988) ≤ ((6582837113 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_722
  obtain ⟨hpl, hph⟩ := kernel_bounds_2563
  obtain ⟨hcl, hch⟩ := kernel_bounds_2564
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2564
  have h : (((410881 / 128 : ℚ) : ℝ) * (logKernel ((2563 / 64 : ℚ) : ℝ) - logKernel ((641 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((641 / 16 : ℚ) : ℝ) + Real.log ((641 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((6582837113 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_723 : ((132976189193746163 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2565 / 64 : ℚ) : ℝ) ∧
    Real.log ((2565 / 64 : ℚ) : ℝ) ≤ ((265952378387492329 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((132976189193746163 / 36028797018963968 : ℚ) : ℝ) ≤ ((2565 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2565 / 64 : ℚ) : ℝ) ≤ Real.exp ((265952378387492329 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_723 : heightPower (723 : Fin 988) ≤ ((3273084105716975 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_723
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_723 : heightFactor (723 : Fin 988) ≤ ((3209730861 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_723
  obtain ⟨hpl, hph⟩ := kernel_bounds_2564
  obtain ⟨hcl, hch⟩ := kernel_bounds_2565
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2565
  have h : (((6579225 / 2048 : ℚ) : ℝ) * (logKernel ((641 / 16 : ℚ) : ℝ) - logKernel ((2565 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2565 / 64 : ℚ) : ℝ) + Real.log ((2565 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((3209730861 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_724 : ((265980465542023709 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1283 / 32 : ℚ) : ℝ) ∧
    Real.log ((1283 / 32 : ℚ) : ℝ) ≤ ((8311889548188241 / 2251799813685248 : ℚ) : ℝ) := by
  have hl : Real.exp ((265980465542023709 / 72057594037927936 : ℚ) : ℝ) ≤ ((1283 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1283 / 32 : ℚ) : ℝ) ≤ Real.exp ((8311889548188241 / 2251799813685248 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_724 : heightPower (724 : Fin 988) ≤ ((819397966918867 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_724
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_724 : heightFactor (724 : Fin 988) ≤ ((6260138865 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_724
  obtain ⟨hpl, hph⟩ := kernel_bounds_2565
  obtain ⟨hcl, hch⟩ := kernel_bounds_2566
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2566
  have h : (((1646089 / 512 : ℚ) : ℝ) * (logKernel ((2565 / 64 : ℚ) : ℝ) - logKernel ((1283 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1283 / 32 : ℚ) : ℝ) + Real.log ((1283 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((6260138865 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_725 : ((266008541752796961 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2567 / 64 : ℚ) : ℝ) ∧
    Real.log ((2567 / 64 : ℚ) : ℝ) ≤ ((66502135438199241 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((266008541752796961 / 72057594037927936 : ℚ) : ℝ) ≤ ((2567 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2567 / 64 : ℚ) : ℝ) ≤ Real.exp ((66502135438199241 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_725 : heightPower (725 : Fin 988) ≤ ((3282099586884905 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_725
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_725 : heightFactor (725 : Fin 988) ≤ ((6104768075 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_725
  obtain ⟨hpl, hph⟩ := kernel_bounds_2566
  obtain ⟨hcl, hch⟩ := kernel_bounds_2567
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2567
  have h : (((6589489 / 2048 : ℚ) : ℝ) * (logKernel ((1283 / 32 : ℚ) : ℝ) - logKernel ((2567 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2567 / 64 : ℚ) : ℝ) + Real.log ((2567 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((6104768075 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_726 : ((266036607028336919 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((321 / 8 : ℚ) : ℝ) ∧
    Real.log ((321 / 8 : ℚ) : ℝ) ≤ ((133018303514168461 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((266036607028336919 / 72057594037927936 : ℚ) : ℝ) ≤ ((321 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((321 / 8 : ℚ) : ℝ) ≤ Real.exp ((133018303514168461 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_726 : heightPower (726 : Fin 988) ≤ ((3286607263378587 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_726
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_726 : heightFactor (726 : Fin 988) ≤ ((5953251375 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_726
  obtain ⟨hpl, hph⟩ := kernel_bounds_2567
  obtain ⟨hcl, hch⟩ := kernel_bounds_2568
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2568
  have h : (((103041 / 32 : ℚ) : ℝ) * (logKernel ((2567 / 64 : ℚ) : ℝ) - logKernel ((321 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((321 / 8 : ℚ) : ℝ) + Real.log ((321 / 8 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((5953251375 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_727 : ((133032330688579231 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2569 / 64 : ℚ) : ℝ) ∧
    Real.log ((2569 / 64 : ℚ) : ℝ) ≤ ((266064661377158465 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((133032330688579231 / 36028797018963968 : ℚ) : ℝ) ≤ ((2569 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2569 / 64 : ℚ) : ℝ) ≤ Real.exp ((266064661377158465 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_727 : heightPower (727 : Fin 988) ≤ ((3291114897189775 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_727
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_727 : heightFactor (727 : Fin 988) ≤ ((5805493215 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_727
  obtain ⟨hpl, hph⟩ := kernel_bounds_2568
  obtain ⟨hcl, hch⟩ := kernel_bounds_2569
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2569
  have h : (((6599761 / 2048 : ℚ) : ℝ) * (logKernel ((321 / 8 : ℚ) : ℝ) - logKernel ((2569 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2569 / 64 : ℚ) : ℝ) + Real.log ((2569 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((5805493215 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_728 : ((519712314077669 / 140737488355328 : ℚ) : ℝ) ≤ Real.log ((1285 / 32 : ℚ) : ℝ) ∧
    Real.log ((1285 / 32 : ℚ) : ℝ) ≤ ((266092704807766531 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((519712314077669 / 140737488355328 : ℚ) : ℝ) ≤ ((1285 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1285 / 32 : ℚ) : ℝ) ≤ Real.exp ((266092704807766531 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_728 : heightPower (728 : Fin 988) ≤ ((823905622087923 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_728
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_728 : heightFactor (728 : Fin 988) ≤ ((2830700207 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_728
  obtain ⟨hpl, hph⟩ := kernel_bounds_2569
  obtain ⟨hcl, hch⟩ := kernel_bounds_2570
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2570
  have h : (((1651225 / 512 : ℚ) : ℝ) * (logKernel ((2569 / 64 : ℚ) : ℝ) - logKernel ((1285 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1285 / 32 : ℚ) : ℝ) + Real.log ((1285 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((2830700207 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_729 : ((1039534130190063 / 281474976710656 : ℚ) : ℝ) ≤ Real.log ((2571 / 64 : ℚ) : ℝ) ∧
    Real.log ((2571 / 64 : ℚ) : ℝ) ≤ ((266120737328656131 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((1039534130190063 / 281474976710656 : ℚ) : ℝ) ≤ ((2571 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2571 / 64 : ℚ) : ℝ) ≤ Real.exp ((266120737328656131 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_729 : heightPower (729 : Fin 988) ≤ ((3300130036897521 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_729
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_729 : heightFactor (729 : Fin 988) ≤ ((5520882097 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_729
  obtain ⟨hpl, hph⟩ := kernel_bounds_2570
  obtain ⟨hcl, hch⟩ := kernel_bounds_2571
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2571
  have h : (((6610041 / 2048 : ℚ) : ℝ) * (logKernel ((1285 / 32 : ℚ) : ℝ) - logKernel ((2571 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2571 / 64 : ℚ) : ℝ) + Real.log ((2571 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((5520882097 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_730 : ((66537189737078091 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((643 / 16 : ℚ) : ℝ) ∧
    Real.log ((643 / 16 : ℚ) : ℝ) ≤ ((266148758948312367 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((66537189737078091 / 18014398509481984 : ℚ) : ℝ) ≤ ((643 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((643 / 16 : ℚ) : ℝ) ≤ Real.exp ((266148758948312367 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_730 : heightPower (730 : Fin 988) ≤ ((3304637542860407 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_730
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_730 : heightFactor (730 : Fin 988) ≤ ((1345962411 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_730
  obtain ⟨hpl, hph⟩ := kernel_bounds_2571
  obtain ⟨hcl, hch⟩ := kernel_bounds_2572
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2572
  have h : (((413449 / 128 : ℚ) : ℝ) * (logKernel ((2571 / 64 : ℚ) : ℝ) - logKernel ((643 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((643 / 16 : ℚ) : ℝ) + Real.log ((643 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1345962411 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_731 : ((133088384837605221 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2573 / 64 : ℚ) : ℝ) ∧
    Real.log ((2573 / 64 : ℚ) : ℝ) ≤ ((266176769675210445 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((133088384837605221 / 36028797018963968 : ℚ) : ℝ) ≤ ((2573 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2573 / 64 : ℚ) : ℝ) ≤ Real.exp ((266176769675210445 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_731 : heightPower (731 : Fin 988) ≤ ((206821562892091 / 17592186044416 : ℚ) : ℝ) := by
  have hh := log_height_bounds_731
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_731 : heightFactor (731 : Fin 988) ≤ ((5250216627 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_731
  obtain ⟨hpl, hph⟩ := kernel_bounds_2572
  obtain ⟨hcl, hch⟩ := kernel_bounds_2573
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2573
  have h : (((6620329 / 2048 : ℚ) : ℝ) * (logKernel ((643 / 16 : ℚ) : ℝ) - logKernel ((2573 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2573 / 64 : ℚ) : ℝ) + Real.log ((2573 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((5250216627 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_732 : ((33275596189726961 / 9007199254740992 : ℚ) : ℝ) ≤ Real.log ((1287 / 32 : ℚ) : ℝ) ∧
    Real.log ((1287 / 32 : ℚ) : ℝ) ≤ ((266204769517815691 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((33275596189726961 / 9007199254740992 : ℚ) : ℝ) ≤ ((1287 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1287 / 32 : ℚ) : ℝ) ≤ Real.exp ((266204769517815691 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_732 : heightPower (732 : Fin 988) ≤ ((3313652427169737 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_732
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_732 : heightFactor (732 : Fin 988) ≤ ((1279974691 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_732
  obtain ⟨hpl, hph⟩ := kernel_bounds_2573
  obtain ⟨hcl, hch⟩ := kernel_bounds_2574
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2574
  have h : (((1656369 / 512 : ℚ) : ℝ) * (logKernel ((2573 / 64 : ℚ) : ℝ) - logKernel ((1287 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1287 / 32 : ℚ) : ℝ) + Real.log ((1287 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1279974691 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_733 : ((266232758484583563 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2575 / 64 : ℚ) : ℝ) ∧
    Real.log ((2575 / 64 : ℚ) : ℝ) ≤ ((133116379242291783 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((266232758484583563 / 72057594037927936 : ℚ) : ℝ) ≤ ((2575 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2575 / 64 : ℚ) : ℝ) ≤ Real.exp ((133116379242291783 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_733 : heightPower (733 : Fin 988) ≤ ((1659079902791139 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_733
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_733 : heightFactor (733 : Fin 988) ≤ ((2496406929 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_733
  obtain ⟨hpl, hph⟩ := kernel_bounds_2574
  obtain ⟨hcl, hch⟩ := kernel_bounds_2575
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2575
  have h : (((6630625 / 2048 : ℚ) : ℝ) * (logKernel ((1287 / 32 : ℚ) : ℝ) - logKernel ((2575 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2575 / 64 : ℚ) : ℝ) + Real.log ((2575 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((2496406929 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_734 : ((133130368291979841 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((161 / 4 : ℚ) : ℝ) ∧
    Real.log ((161 / 4 : ℚ) : ℝ) ≤ ((266260736583959685 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((133130368291979841 / 36028797018963968 : ℚ) : ℝ) ≤ ((161 / 4 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((161 / 4 : ℚ) : ℝ) ≤ Real.exp ((266260736583959685 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_734 : heightPower (734 : Fin 988) ≤ ((1661333570772035 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_734
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_734 : heightFactor (734 : Fin 988) ≤ ((2434440875 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_734
  obtain ⟨hpl, hph⟩ := kernel_bounds_2575
  obtain ⟨hcl, hch⟩ := kernel_bounds_2576
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2576
  have h : (((25921 / 8 : ℚ) : ℝ) * (logKernel ((2575 / 64 : ℚ) : ℝ) - logKernel ((161 / 4 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((161 / 4 : ℚ) : ℝ) + Real.log ((161 / 4 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((2434440875 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_735 : ((266288703824379821 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2577 / 64 : ℚ) : ℝ) ∧
    Real.log ((2577 / 64 : ℚ) : ℝ) ≤ ((16643043989023739 / 4503599627370496 : ℚ) : ℝ) := by
  have hl : Real.exp ((266288703824379821 / 72057594037927936 : ℚ) : ℝ) ≤ ((2577 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2577 / 64 : ℚ) : ℝ) ≤ Real.exp ((16643043989023739 / 4503599627370496 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_735 : heightPower (735 : Fin 988) ≤ ((3327174435088065 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_735
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_735 : heightFactor (735 : Fin 988) ≤ ((1187006067 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_735
  obtain ⟨hpl, hph⟩ := kernel_bounds_2576
  obtain ⟨hcl, hch⟩ := kernel_bounds_2577
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2577
  have h : (((6640929 / 2048 : ℚ) : ℝ) * (logKernel ((161 / 4 : ℚ) : ℝ) - logKernel ((2577 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2577 / 64 : ℚ) : ℝ) + Real.log ((2577 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1187006067 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

end LegendreK6.M2Pilot.Enclosures.Height022
