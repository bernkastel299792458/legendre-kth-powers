import LegendreK6.M2PilotDefinitions
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp

/-! Generated proposals: every bound is checked by Lean, not by trusting Arb. -/
namespace LegendreK6.M2Pilot.Enclosures.Height011
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem height_z_bounds_2193 : ((36546741304731343 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2193 / 64 : ℚ) : ℝ) ∧
    heightZ ((2193 / 64 : ℚ) : ℝ) ≤ ((18273370652365673 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((36546741304731343 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2193 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-851 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2193 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-851 / 192 : ℚ) : ℝ) ≤ ((18273370652365673 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2193 : ((18685550138913 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2193 / 64 : ℚ) : ℝ) ∧
    logKernel ((2193 / 64 : ℚ) : ℝ) ≤ ((37371100277831 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2193
  constructor
  · exact (show ((18685550138913 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((36546741304731343 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2193 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((18273370652365673 / 9223372036854775808 : ℚ) : ℝ) ≤ ((37371100277831 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2194 : ((17990068299333199 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((1097 / 32 : ℚ) : ℝ) ∧
    heightZ ((1097 / 32 : ℚ) : ℝ) ≤ ((35980136598666401 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((17990068299333199 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((1097 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-427 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1097 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-427 / 96 : ℚ) : ℝ) ≤ ((35980136598666401 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2194 : ((36221312398217 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1097 / 32 : ℚ) : ℝ) ∧
    logKernel ((1097 / 32 : ℚ) : ℝ) ≤ ((18110656199111 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2194
  constructor
  · exact (show ((36221312398217 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((17990068299333199 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1097 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((35980136598666401 / 18446744073709551616 : ℚ) : ℝ) ≤ ((18110656199111 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2195 : ((35422316284354963 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2195 / 64 : ℚ) : ℝ) ∧
    heightZ ((2195 / 64 : ℚ) : ℝ) ≤ ((17711158142177483 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((35422316284354963 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2195 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-857 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2195 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-857 / 192 : ℚ) : ℝ) ≤ ((17711158142177483 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2195 : ((17553449886351 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2195 / 64 : ℚ) : ℝ) ∧
    logKernel ((2195 / 64 : ℚ) : ℝ) ≤ ((35106899772707 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2195
  constructor
  · exact (show ((17553449886351 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((35422316284354963 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2195 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((17711158142177483 / 9223372036854775808 : ℚ) : ℝ) ≤ ((35106899772707 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2196 : ((17436572086213059 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((549 / 16 : ℚ) : ℝ) ∧
    heightZ ((549 / 16 : ℚ) : ℝ) ≤ ((34873144172426121 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((17436572086213059 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((549 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-215 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((549 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-215 / 48 : ℚ) : ℝ) ≤ ((34873144172426121 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2196 : ((34026774019133 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((549 / 16 : ℚ) : ℝ) ∧
    logKernel ((549 / 16 : ℚ) : ℝ) ≤ ((17013387009569 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2196
  constructor
  · exact (show ((34026774019133 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((17436572086213059 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((549 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((34873144172426121 / 18446744073709551616 : ℚ) : ℝ) ≤ ((17013387009569 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2197 : ((34332486184929435 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2197 / 64 : ℚ) : ℝ) ∧
    heightZ ((2197 / 64 : ℚ) : ℝ) ≤ ((17166243092464719 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((34332486184929435 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2197 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-863 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2197 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-863 / 192 : ℚ) : ℝ) ≤ ((17166243092464719 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2197 : ((2061242515085 / 4503599627370496 : ℚ) : ℝ) ≤ logKernel ((2197 / 64 : ℚ) : ℝ) ∧
    logKernel ((2197 / 64 : ℚ) : ℝ) ≤ ((32979880241365 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2197
  constructor
  · exact (show ((2061242515085 / 4503599627370496 : ℚ) : ℝ) ≤ zKernel ((34332486184929435 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2197 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((17166243092464719 / 9223372036854775808 : ℚ) : ℝ) ≤ ((32979880241365 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2198 : ((8450052580650109 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((1099 / 32 : ℚ) : ℝ) ∧
    heightZ ((1099 / 32 : ℚ) : ℝ) ≤ ((33800210322600439 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((8450052580650109 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((1099 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-433 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1099 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-433 / 96 : ℚ) : ℝ) ≤ ((33800210322600439 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2198 : ((31965195998975 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1099 / 32 : ℚ) : ℝ) ∧
    logKernel ((1099 / 32 : ℚ) : ℝ) ≤ ((7991298999745 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2198
  constructor
  · exact (show ((31965195998975 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((8450052580650109 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1099 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((33800210322600439 / 18446744073709551616 : ℚ) : ℝ) ≤ ((7991298999745 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2199 : ((33276186632633555 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2199 / 64 : ℚ) : ℝ) ∧
    heightZ ((2199 / 64 : ℚ) : ℝ) ≤ ((16638093316316779 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((33276186632633555 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2199 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-869 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2199 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-869 / 192 : ℚ) : ℝ) ≤ ((16638093316316779 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2199 : ((30981730308757 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2199 / 64 : ℚ) : ℝ) ∧
    logKernel ((2199 / 64 : ℚ) : ℝ) ≤ ((15490865154381 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2199
  constructor
  · exact (show ((30981730308757 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((33276186632633555 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2199 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((16638093316316779 / 9223372036854775808 : ℚ) : ℝ) ≤ ((15490865154381 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2200 : ((16380143588477367 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((275 / 8 : ℚ) : ℝ) ∧
    heightZ ((275 / 8 : ℚ) : ℝ) ≤ ((32760287176954737 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((16380143588477367 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((275 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-109 / 24 : ℚ) : ℝ) ∧
      Real.exp (-((275 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-109 / 24 : ℚ) : ℝ) ≤ ((32760287176954737 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2200 : ((15014261338415 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((275 / 8 : ℚ) : ℝ) ∧
    logKernel ((275 / 8 : ℚ) : ℝ) ≤ ((30028522676835 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2200
  constructor
  · exact (show ((15014261338415 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((16380143588477367 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((275 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((32760287176954737 / 18446744073709551616 : ℚ) : ℝ) ≤ ((30028522676835 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2201 : ((32252386000985905 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2201 / 64 : ℚ) : ℝ) ∧
    heightZ ((2201 / 64 : ℚ) : ℝ) ≤ ((8063096500246477 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((32252386000985905 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2201 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-875 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2201 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-875 / 192 : ℚ) : ℝ) ≤ ((8063096500246477 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2201 : ((14552321080305 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2201 / 64 : ℚ) : ℝ) ∧
    logKernel ((2201 / 64 : ℚ) : ℝ) ≤ ((29104642160615 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2201
  constructor
  · exact (show ((14552321080305 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((32252386000985905 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2201 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((8063096500246477 / 4611686018427387904 : ℚ) : ℝ) ≤ ((29104642160615 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2202 : ((3969044887861717 / 2305843009213693952 : ℚ) : ℝ) ≤ heightZ ((1101 / 32 : ℚ) : ℝ) ∧
    heightZ ((1101 / 32 : ℚ) : ℝ) ≤ ((31752359102893739 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((3969044887861717 / 2305843009213693952 : ℚ) : ℝ) ≤ Real.exp (-((1101 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-439 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1101 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-439 / 96 : ℚ) : ℝ) ≤ ((31752359102893739 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2202 : ((28209186459605 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1101 / 32 : ℚ) : ℝ) ∧
    logKernel ((1101 / 32 : ℚ) : ℝ) ≤ ((14104593229805 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2202
  constructor
  · exact (show ((28209186459605 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((3969044887861717 / 2305843009213693952 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1101 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((31752359102893739 / 18446744073709551616 : ℚ) : ℝ) ≤ ((14104593229805 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2203 : ((31260084403315129 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2203 / 64 : ℚ) : ℝ) ∧
    heightZ ((2203 / 64 : ℚ) : ℝ) ≤ ((7815021100828783 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((31260084403315129 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2203 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-881 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2203 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-881 / 192 : ℚ) : ℝ) ≤ ((7815021100828783 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2203 : ((27341281034189 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2203 / 64 : ℚ) : ℝ) ∧
    logKernel ((2203 / 64 : ℚ) : ℝ) ≤ ((13670640517097 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2203
  constructor
  · exact (show ((27341281034189 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((31260084403315129 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2203 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((7815021100828783 / 4611686018427387904 : ℚ) : ℝ) ≤ ((13670640517097 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2204 : ((30775441715552083 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((551 / 16 : ℚ) : ℝ) ∧
    heightZ ((551 / 16 : ℚ) : ℝ) ≤ ((15387720857776043 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((30775441715552083 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((551 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-221 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((551 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-221 / 48 : ℚ) : ℝ) ≤ ((15387720857776043 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2204 : ((13250039125747 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((551 / 16 : ℚ) : ℝ) ∧
    logKernel ((551 / 16 : ℚ) : ℝ) ≤ ((26500078251499 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2204
  constructor
  · exact (show ((13250039125747 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((30775441715552083 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((551 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((15387720857776043 / 9223372036854775808 : ℚ) : ℝ) ≤ ((26500078251499 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2205 : ((30298312716228639 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2205 / 64 : ℚ) : ℝ) ∧
    heightZ ((2205 / 64 : ℚ) : ℝ) ≤ ((15149156358114321 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((30298312716228639 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2205 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-887 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2205 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-887 / 192 : ℚ) : ℝ) ≤ ((15149156358114321 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2205 : ((25684756557571 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2205 / 64 : ℚ) : ℝ) ∧
    logKernel ((2205 / 64 : ℚ) : ℝ) ≤ ((3210594569697 / 9007199254740992 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2205
  constructor
  · exact (show ((25684756557571 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((30298312716228639 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2205 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((15149156358114321 / 9223372036854775808 : ℚ) : ℝ) ≤ ((3210594569697 / 9007199254740992 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2206 : ((29828580916402753 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1103 / 32 : ℚ) : ℝ) ∧
    heightZ ((1103 / 32 : ℚ) : ℝ) ≤ ((7457145229100689 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((29828580916402753 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1103 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-445 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1103 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-445 / 96 : ℚ) : ℝ) ≤ ((7457145229100689 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2206 : ((3111814959379 / 9007199254740992 : ℚ) : ℝ) ≤ logKernel ((1103 / 32 : ℚ) : ℝ) ∧
    logKernel ((1103 / 32 : ℚ) : ℝ) ≤ ((24894519675037 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2206
  constructor
  · exact (show ((3111814959379 / 9007199254740992 : ℚ) : ℝ) ≤ zKernel ((29828580916402753 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1103 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((7457145229100689 / 4611686018427387904 : ℚ) : ℝ) ≤ ((24894519675037 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2207 : ((14683065816563015 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2207 / 64 : ℚ) : ℝ) ∧
    heightZ ((2207 / 64 : ℚ) : ℝ) ≤ ((29366131633126033 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((14683065816563015 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2207 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-893 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2207 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-893 / 192 : ℚ) : ℝ) ≤ ((29366131633126033 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2207 : ((24128595825367 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2207 / 64 : ℚ) : ℝ) ∧
    logKernel ((2207 / 64 : ℚ) : ℝ) ≤ ((6032148956343 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2207
  constructor
  · exact (show ((24128595825367 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((14683065816563015 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2207 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((29366131633126033 / 18446744073709551616 : ℚ) : ℝ) ≤ ((6032148956343 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2208 : ((3613856495180549 / 2305843009213693952 : ℚ) : ℝ) ≤ heightZ ((69 / 2 : ℚ) : ℝ) ∧
    heightZ ((69 / 2 : ℚ) : ℝ) ≤ ((28910851961444395 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((3613856495180549 / 2305843009213693952 : ℚ) : ℝ) ≤ Real.exp (-((69 / 2 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-14 / 3 : ℚ) : ℝ) ∧
      Real.exp (-((69 / 2 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-14 / 3 : ℚ) : ℝ) ≤ ((28910851961444395 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2208 : ((2923279621899 / 9007199254740992 : ℚ) : ℝ) ≤ logKernel ((69 / 2 : ℚ) : ℝ) ∧
    logKernel ((69 / 2 : ℚ) : ℝ) ≤ ((23386236975197 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2208
  constructor
  · exact (show ((2923279621899 / 9007199254740992 : ℚ) : ℝ) ≤ zKernel ((3613856495180549 / 2305843009213693952 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((69 / 2 : ℚ) : ℝ)) hh).trans
      (show zKernel ((28910851961444395 / 18446744073709551616 : ℚ) : ℝ) ≤ ((23386236975197 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2209 : ((28462630746832827 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2209 / 64 : ℚ) : ℝ) ∧
    heightZ ((2209 / 64 : ℚ) : ℝ) ≤ ((14231315373416415 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((28462630746832827 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2209 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-899 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2209 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-899 / 192 : ℚ) : ℝ) ≤ ((14231315373416415 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2209 : ((708334940803 / 2251799813685248 : ℚ) : ℝ) ≤ logKernel ((2209 / 64 : ℚ) : ℝ) ∧
    logKernel ((2209 / 64 : ℚ) : ℝ) ≤ ((22666718105701 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2209
  constructor
  · exact (show ((708334940803 / 2251799813685248 : ℚ) : ℝ) ≤ zKernel ((28462630746832827 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2209 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((14231315373416415 / 9223372036854775808 : ℚ) : ℝ) ≤ ((22666718105701 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2210 : ((875667454939297 / 576460752303423488 : ℚ) : ℝ) ≤ heightZ ((1105 / 32 : ℚ) : ℝ) ∧
    heightZ ((1105 / 32 : ℚ) : ℝ) ≤ ((28021358558057507 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((875667454939297 / 576460752303423488 : ℚ) : ℝ) ≤ Real.exp (-((1105 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-451 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1105 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-451 / 96 : ℚ) : ℝ) ≤ ((28021358558057507 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2210 : ((21969336504547 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1105 / 32 : ℚ) : ℝ) ∧
    logKernel ((1105 / 32 : ℚ) : ℝ) ≤ ((2746167063069 / 9007199254740992 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2210
  constructor
  · exact (show ((21969336504547 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((875667454939297 / 576460752303423488 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1105 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((28021358558057507 / 18446744073709551616 : ℚ) : ℝ) ≤ ((2746167063069 / 9007199254740992 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2211 : ((27586927660458621 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2211 / 64 : ℚ) : ℝ) ∧
    heightZ ((2211 / 64 : ℚ) : ℝ) ≤ ((215522872347333 / 144115188075855872 : ℚ) : ℝ) := by
  have h : ((27586927660458621 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2211 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-905 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2211 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-905 / 192 : ℚ) : ℝ) ≤ ((215522872347333 / 144115188075855872 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2211 : ((21293411079601 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2211 / 64 : ℚ) : ℝ) ∧
    logKernel ((2211 / 64 : ℚ) : ℝ) ≤ ((10646705539803 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2211
  constructor
  · exact (show ((21293411079601 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((27586927660458621 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2211 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((215522872347333 / 144115188075855872 : ℚ) : ℝ) ≤ ((10646705539803 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2212 : ((6789807997411865 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((553 / 16 : ℚ) : ℝ) ∧
    heightZ ((553 / 16 : ℚ) : ℝ) ≤ ((27159231989647463 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((6789807997411865 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((553 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-227 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((553 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-227 / 48 : ℚ) : ℝ) ≤ ((27159231989647463 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2212 : ((5159570423429 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((553 / 16 : ℚ) : ℝ) ∧
    logKernel ((553 / 16 : ℚ) : ℝ) ≤ ((20638281693721 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2212
  constructor
  · exact (show ((5159570423429 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((6789807997411865 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((553 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((27159231989647463 / 18446744073709551616 : ℚ) : ℝ) ≤ ((20638281693721 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2213 : ((26738167125611233 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2213 / 64 : ℚ) : ℝ) ∧
    heightZ ((2213 / 64 : ℚ) : ℝ) ≤ ((6684541781402809 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((26738167125611233 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2213 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-911 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2213 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-911 / 192 : ℚ) : ℝ) ≤ ((6684541781402809 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2213 : ((20003308520035 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2213 / 64 : ℚ) : ℝ) ∧
    logKernel ((2213 / 64 : ℚ) : ℝ) ≤ ((2500413565005 / 9007199254740992 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2213
  constructor
  · exact (show ((20003308520035 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((26738167125611233 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2213 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((6684541781402809 / 4611686018427387904 : ℚ) : ℝ) ≤ ((2500413565005 / 9007199254740992 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2214 : ((26323630267219401 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1107 / 32 : ℚ) : ℝ) ∧
    heightZ ((1107 / 32 : ℚ) : ℝ) ≤ ((6580907566804851 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((26323630267219401 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1107 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-457 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1107 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-457 / 96 : ℚ) : ℝ) ≤ ((6580907566804851 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2214 : ((19387871417101 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1107 / 32 : ℚ) : ℝ) ∧
    logKernel ((1107 / 32 : ℚ) : ℝ) ≤ ((9693935708553 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2214
  constructor
  · exact (show ((19387871417101 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((26323630267219401 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1107 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((6580907566804851 / 4611686018427387904 : ℚ) : ℝ) ≤ ((9693935708553 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2215 : ((25915520207125227 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2215 / 64 : ℚ) : ℝ) ∧
    heightZ ((2215 / 64 : ℚ) : ℝ) ≤ ((12957760103562615 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((25915520207125227 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2215 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-917 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2215 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-917 / 192 : ℚ) : ℝ) ≤ ((12957760103562615 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2215 : ((2348921165401 / 9007199254740992 : ℚ) : ℝ) ≤ logKernel ((2215 / 64 : ℚ) : ℝ) ∧
    logKernel ((2215 / 64 : ℚ) : ℝ) ≤ ((18791369323213 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2215
  constructor
  · exact (show ((2348921165401 / 9007199254740992 : ℚ) : ℝ) ≤ zKernel ((25915520207125227 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2215 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((12957760103562615 / 9223372036854775808 : ℚ) : ℝ) ≤ ((18791369323213 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2216 : ((12756868653528225 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((277 / 8 : ℚ) : ℝ) ∧
    heightZ ((277 / 8 : ℚ) : ℝ) ≤ ((25513737307056453 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((12756868653528225 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((277 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-115 / 24 : ℚ) : ℝ) ∧
      Real.exp (-((277 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-115 / 24 : ℚ) : ℝ) ≤ ((25513737307056453 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2216 : ((18213219669373 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((277 / 8 : ℚ) : ℝ) ∧
    logKernel ((277 / 8 : ℚ) : ℝ) ≤ ((9106609834689 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2216
  constructor
  · exact (show ((18213219669373 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((12756868653528225 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((277 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((25513737307056453 / 18446744073709551616 : ℚ) : ℝ) ≤ ((9106609834689 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2217 : ((25118183473489039 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2217 / 64 : ℚ) : ℝ) ∧
    heightZ ((2217 / 64 : ℚ) : ℝ) ≤ ((12559091736744521 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((25118183473489039 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2217 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-923 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2217 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-923 / 192 : ℚ) : ℝ) ≤ ((12559091736744521 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2217 : ((8826428905187 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2217 / 64 : ℚ) : ℝ) ∧
    logKernel ((2217 / 64 : ℚ) : ℝ) ≤ ((17652857810379 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2217
  constructor
  · exact (show ((8826428905187 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((25118183473489039 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2217 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((12559091736744521 / 9223372036854775808 : ℚ) : ℝ) ≤ ((17652857810379 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2218 : ((6182190533424523 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((1109 / 32 : ℚ) : ℝ) ∧
    heightZ ((1109 / 32 : ℚ) : ℝ) ≤ ((24728762133698095 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((6182190533424523 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((1109 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-463 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1109 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-463 / 96 : ℚ) : ℝ) ≤ ((24728762133698095 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2218 : ((4277434118325 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((1109 / 32 : ℚ) : ℝ) ∧
    logKernel ((1109 / 32 : ℚ) : ℝ) ≤ ((17109736473305 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2218
  constructor
  · exact (show ((4277434118325 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((6182190533424523 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1109 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((24728762133698095 / 18446744073709551616 : ℚ) : ℝ) ≤ ((17109736473305 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2219 : ((380396534565313 / 288230376151711744 : ℚ) : ℝ) ≤ heightZ ((2219 / 64 : ℚ) : ℝ) ∧
    heightZ ((2219 / 64 : ℚ) : ℝ) ≤ ((24345378212180035 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((380396534565313 / 288230376151711744 : ℚ) : ℝ) ≤ Real.exp (-((2219 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-929 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2219 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-929 / 192 : ℚ) : ℝ) ≤ ((24345378212180035 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2219 : ((8291662611527 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2219 / 64 : ℚ) : ℝ) ∧
    logKernel ((2219 / 64 : ℚ) : ℝ) ≤ ((16583325223059 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2219
  constructor
  · exact (show ((8291662611527 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((380396534565313 / 288230376151711744 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2219 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((24345378212180035 / 18446744073709551616 : ℚ) : ℝ) ≤ ((16583325223059 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2220 : ((23967938107440341 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((555 / 16 : ℚ) : ℝ) ∧
    heightZ ((555 / 16 : ℚ) : ℝ) ≤ ((2995992263430043 / 2305843009213693952 : ℚ) : ℝ) := by
  have h : ((23967938107440341 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((555 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-233 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((555 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-233 / 48 : ℚ) : ℝ) ≤ ((2995992263430043 / 2305843009213693952 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2220 : ((8036554972157 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((555 / 16 : ℚ) : ℝ) ∧
    logKernel ((555 / 16 : ℚ) : ℝ) ≤ ((16073109944319 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2220
  constructor
  · exact (show ((8036554972157 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((23967938107440341 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((555 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((2995992263430043 / 2305843009213693952 : ℚ) : ℝ) ≤ ((16073109944319 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2221 : ((1474771854321323 / 1152921504606846976 : ℚ) : ℝ) ≤ heightZ ((2221 / 64 : ℚ) : ℝ) ∧
    heightZ ((2221 / 64 : ℚ) : ℝ) ≤ ((23596349669141171 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((1474771854321323 / 1152921504606846976 : ℚ) : ℝ) ≤ Real.exp (-((2221 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-935 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2221 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-935 / 192 : ℚ) : ℝ) ≤ ((23596349669141171 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2221 : ((15578592339421 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2221 / 64 : ℚ) : ℝ) ∧
    logKernel ((2221 / 64 : ℚ) : ℝ) ≤ ((7789296169713 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2221
  constructor
  · exact (show ((15578592339421 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((1474771854321323 / 1152921504606846976 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2221 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((23596349669141171 / 18446744073709551616 : ℚ) : ℝ) ≤ ((7789296169713 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2222 : ((23230522175603227 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1111 / 32 : ℚ) : ℝ) ∧
    heightZ ((1111 / 32 : ℚ) : ℝ) ≤ ((11615261087801615 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((23230522175603227 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1111 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-469 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1111 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-469 / 96 : ℚ) : ℝ) ≤ ((11615261087801615 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2222 : ((7549644720863 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((1111 / 32 : ℚ) : ℝ) ∧
    logKernel ((1111 / 32 : ℚ) : ℝ) ≤ ((15099289441731 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2222
  constructor
  · exact (show ((7549644720863 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((23230522175603227 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1111 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((11615261087801615 / 9223372036854775808 : ℚ) : ℝ) ≤ ((15099289441731 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2223 : ((22870366311656505 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2223 / 64 : ℚ) : ℝ) ∧
    heightZ ((2223 / 64 : ℚ) : ℝ) ≤ ((5717591577914127 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((22870366311656505 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2223 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-941 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2223 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-941 / 192 : ℚ) : ℝ) ≤ ((5717591577914127 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2223 : ((7317366571949 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2223 / 64 : ℚ) : ℝ) ∧
    logKernel ((2223 / 64 : ℚ) : ℝ) ≤ ((14634733143903 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2223
  constructor
  · exact (show ((7317366571949 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((22870366311656505 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2223 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((5717591577914127 / 4611686018427387904 : ℚ) : ℝ) ≤ ((14634733143903 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2224 : ((22515794146834353 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((139 / 4 : ℚ) : ℝ) ∧
    heightZ ((139 / 4 : ℚ) : ℝ) ≤ ((5628948536708589 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((22515794146834353 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((139 / 4 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-59 / 12 : ℚ) : ℝ) ∧
      Real.exp (-((139 / 4 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-59 / 12 : ℚ) : ℝ) ≤ ((5628948536708589 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2224 : ((7092234870379 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((139 / 4 : ℚ) : ℝ) ∧
    logKernel ((139 / 4 : ℚ) : ℝ) ≤ ((14184469740763 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2224
  constructor
  · exact (show ((7092234870379 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((22515794146834353 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((139 / 4 : ℚ) : ℝ)) hh).trans
      (show zKernel ((5628948536708589 / 4611686018427387904 : ℚ) : ℝ) ≤ ((14184469740763 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2225 : ((11083359556952825 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2225 / 64 : ℚ) : ℝ) ∧
    heightZ ((2225 / 64 : ℚ) : ℝ) ≤ ((22166719113905653 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((11083359556952825 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2225 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-947 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2225 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-947 / 192 : ℚ) : ℝ) ≤ ((22166719113905653 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2225 : ((13748059486167 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2225 / 64 : ℚ) : ℝ) ∧
    logKernel ((2225 / 64 : ℚ) : ℝ) ≤ ((3437014871543 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2225
  constructor
  · exact (show ((13748059486167 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((11083359556952825 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2225 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((22166719113905653 / 18446744073709551616 : ℚ) : ℝ) ≤ ((3437014871543 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem log_height_bounds_352 : ((254694667941615537 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1097 / 32 : ℚ) : ℝ) ∧
    Real.log ((1097 / 32 : ℚ) : ℝ) ≤ ((63673666985403885 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((254694667941615537 / 72057594037927936 : ℚ) : ℝ) ≤ ((1097 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1097 / 32 : ℚ) : ℝ) ≤ Real.exp ((63673666985403885 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_352 : heightPower (352 : Fin 988) ≤ ((1597433418668185 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_352
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_352 : heightFactor (352 : Fin 988) ≤ ((17499829701175 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_352
  obtain ⟨hpl, hph⟩ := kernel_bounds_2193
  obtain ⟨hcl, hch⟩ := kernel_bounds_2194
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2194
  have h : (((1203409 / 512 : ℚ) : ℝ) * (logKernel ((2193 / 64 : ℚ) : ℝ) - logKernel ((1097 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1097 / 32 : ℚ) : ℝ) + Real.log ((1097 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((17499829701175 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_353 : ((15920468967679429 / 4503599627370496 : ℚ) : ℝ) ≤ Real.log ((2195 / 64 : ℚ) : ℝ) ∧
    Real.log ((2195 / 64 : ℚ) : ℝ) ≤ ((254727503482870867 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((15920468967679429 / 4503599627370496 : ℚ) : ℝ) ≤ ((2195 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2195 / 64 : ℚ) : ℝ) ≤ Real.exp ((254727503482870867 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_353 : heightPower (353 : Fin 988) ≤ ((800979864506159 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_353
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_353 : heightFactor (353 : Fin 988) ≤ ((34136251985765 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_353
  obtain ⟨hpl, hph⟩ := kernel_bounds_2194
  obtain ⟨hcl, hch⟩ := kernel_bounds_2195
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2195
  have h : (((4818025 / 2048 : ℚ) : ℝ) * (logKernel ((1097 / 32 : ℚ) : ℝ) - logKernel ((2195 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2195 / 64 : ℚ) : ℝ) + Real.log ((2195 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((34136251985765 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_354 : ((254760324068288163 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((549 / 16 : ℚ) : ℝ) ∧
    Real.log ((549 / 16 : ℚ) : ℝ) ≤ ((127380162034144083 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((254760324068288163 / 72057594037927936 : ℚ) : ℝ) ≤ ((549 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((549 / 16 : ℚ) : ℝ) ≤ Real.exp ((127380162034144083 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_354 : heightPower (354 : Fin 988) ≤ ((200810747616901 / 35184372088832 : ℚ) : ℝ) := by
  have hh := log_height_bounds_354
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_354 : heightFactor (354 : Fin 988) ≤ ((66588255725713 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_354
  obtain ⟨hpl, hph⟩ := kernel_bounds_2195
  obtain ⟨hcl, hch⟩ := kernel_bounds_2196
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2196
  have h : (((301401 / 128 : ℚ) : ℝ) * (logKernel ((2195 / 64 : ℚ) : ℝ) - logKernel ((549 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((549 / 16 : ℚ) : ℝ) + Real.log ((549 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((66588255725713 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_355 : ((63698282427871329 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((2197 / 64 : ℚ) : ℝ) ∧
    Real.log ((2197 / 64 : ℚ) : ℝ) ≤ ((254793129711485319 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((63698282427871329 / 18014398509481984 : ℚ) : ℝ) ≤ ((2197 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2197 / 64 : ℚ) : ℝ) ≤ Real.exp ((254793129711485319 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_355 : heightPower (355 : Fin 988) ≤ ((1611012174490051 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_355
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_355 : heightFactor (355 : Fin 988) ≤ ((32472762805429 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_355
  obtain ⟨hpl, hph⟩ := kernel_bounds_2196
  obtain ⟨hcl, hch⟩ := kernel_bounds_2197
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2197
  have h : (((4826809 / 2048 : ℚ) : ℝ) * (logKernel ((549 / 16 : ℚ) : ℝ) - logKernel ((2197 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2197 / 64 : ℚ) : ℝ) + Real.log ((2197 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((32472762805429 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_356 : ((254825920426061613 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1099 / 32 : ℚ) : ℝ) ∧
    Real.log ((1099 / 32 : ℚ) : ℝ) ≤ ((15926620026628851 / 4503599627370496 : ℚ) : ℝ) := by
  have hl : Real.exp ((254825920426061613 / 72057594037927936 : ℚ) : ℝ) ≤ ((1099 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1099 / 32 : ℚ) : ℝ) ≤ Real.exp ((15926620026628851 / 4503599627370496 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_356 : heightPower (356 : Fin 988) ≤ ((1615538309729969 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_356
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_356 : heightFactor (356 : Fin 988) ≤ ((31671645486987 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_356
  obtain ⟨hpl, hph⟩ := kernel_bounds_2197
  obtain ⟨hcl, hch⟩ := kernel_bounds_2198
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2198
  have h : (((1207801 / 512 : ℚ) : ℝ) * (logKernel ((2197 / 64 : ℚ) : ℝ) - logKernel ((1099 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1099 / 32 : ℚ) : ℝ) + Real.log ((1099 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((31671645486987 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_357 : ((254858696225597789 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2199 / 64 : ℚ) : ℝ) ∧
    Real.log ((2199 / 64 : ℚ) : ℝ) ≤ ((7964334257049931 / 2251799813685248 : ℚ) : ℝ) := by
  have hl : Real.exp ((254858696225597789 / 72057594037927936 : ℚ) : ℝ) ≤ ((2199 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2199 / 64 : ℚ) : ℝ) ≤ Real.exp ((7964334257049931 / 2251799813685248 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_357 : heightPower (357 : Fin 988) ≤ ((1620064386708011 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_357
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_357 : heightFactor (357 : Fin 988) ≤ ((61780554330975 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_357
  obtain ⟨hpl, hph⟩ := kernel_bounds_2198
  obtain ⟨hcl, hch⟩ := kernel_bounds_2199
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2199
  have h : (((4835601 / 2048 : ℚ) : ℝ) * (logKernel ((1099 / 32 : ℚ) : ℝ) - logKernel ((2199 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2199 / 64 : ℚ) : ℝ) + Real.log ((2199 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((61780554330975 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_358 : ((127445728561828027 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((275 / 8 : ℚ) : ℝ) ∧
    Real.log ((275 / 8 : ℚ) : ℝ) ≤ ((254891457123656057 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((127445728561828027 / 36028797018963968 : ℚ) : ℝ) ≤ ((275 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((275 / 8 : ℚ) : ℝ) ≤ Real.exp ((254891457123656057 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_358 : heightPower (358 : Fin 988) ≤ ((1624590405477155 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_358
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_358 : heightFactor (358 : Fin 988) ≤ ((30128171373877 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_358
  obtain ⟨hpl, hph⟩ := kernel_bounds_2199
  obtain ⟨hcl, hch⟩ := kernel_bounds_2200
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2200
  have h : (((75625 / 32 : ℚ) : ℝ) * (logKernel ((2199 / 64 : ℚ) : ℝ) - logKernel ((275 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((275 / 8 : ℚ) : ℝ) + Real.log ((275 / 8 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((30128171373877 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_359 : ((7966381347930629 / 2251799813685248 : ℚ) : ℝ) ≤ Real.log ((2201 / 64 : ℚ) : ℝ) ∧
    Real.log ((2201 / 64 : ℚ) : ℝ) ≤ ((254924203133780131 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((7966381347930629 / 2251799813685248 : ℚ) : ℝ) ≤ ((2201 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2201 / 64 : ℚ) : ℝ) ≤ Real.exp ((254924203133780131 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_359 : heightPower (359 : Fin 988) ≤ ((814558183045153 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_359
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_359 : heightFactor (359 : Fin 988) ≤ ((58769707236481 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_359
  obtain ⟨hpl, hph⟩ := kernel_bounds_2200
  obtain ⟨hcl, hch⟩ := kernel_bounds_2201
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2201
  have h : (((4844401 / 2048 : ℚ) : ℝ) * (logKernel ((275 / 8 : ℚ) : ℝ) - logKernel ((2201 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2201 / 64 : ℚ) : ℝ) + Real.log ((2201 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((58769707236481 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_360 : ((63739233567373819 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((1101 / 32 : ℚ) : ℝ) ∧
    Real.log ((1101 / 32 : ℚ) : ℝ) ≤ ((254956934269495279 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((63739233567373819 / 18014398509481984 : ℚ) : ℝ) ≤ ((1101 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1101 / 32 : ℚ) : ℝ) ≤ Real.exp ((254956934269495279 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_360 : heightPower (360 : Fin 988) ≤ ((1633642268600297 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_360
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_360 : heightFactor (360 : Fin 988) ≤ ((28659861083361 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_360
  obtain ⟨hpl, hph⟩ := kernel_bounds_2201
  obtain ⟨hcl, hch⟩ := kernel_bounds_2202
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2202
  have h : (((1212201 / 512 : ℚ) : ℝ) * (logKernel ((2201 / 64 : ℚ) : ℝ) - logKernel ((1101 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1101 / 32 : ℚ) : ℝ) + Real.log ((1101 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((28659861083361 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_361 : ((254989650544308341 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2203 / 64 : ℚ) : ℝ) ∧
    Real.log ((2203 / 64 : ℚ) : ℝ) ≤ ((31873706318038543 / 9007199254740992 : ℚ) : ℝ) := by
  have hl : Real.exp ((254989650544308341 / 72057594037927936 : ℚ) : ℝ) ≤ ((2203 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2203 / 64 : ℚ) : ℝ) ≤ Real.exp ((31873706318038543 / 9007199254740992 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_361 : heightPower (361 : Fin 988) ≤ ((819084056529945 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_361
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_361 : heightFactor (361 : Fin 988) ≤ ((55905484691035 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_361
  obtain ⟨hpl, hph⟩ := kernel_bounds_2202
  obtain ⟨hcl, hch⟩ := kernel_bounds_2203
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2203
  have h : (((4853209 / 2048 : ℚ) : ℝ) * (logKernel ((1101 / 32 : ℚ) : ℝ) - logKernel ((2203 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2203 / 64 : ℚ) : ℝ) + Real.log ((2203 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((55905484691035 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_362 : ((127511175985853887 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((551 / 16 : ℚ) : ℝ) ∧
    Real.log ((551 / 16 : ℚ) : ℝ) ≤ ((255022351971707777 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((127511175985853887 / 36028797018963968 : ℚ) : ℝ) ≤ ((551 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((551 / 16 : ℚ) : ℝ) ≤ Real.exp ((255022351971707777 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_362 : heightPower (362 : Fin 988) ≤ ((1642693899521773 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_362
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_362 : heightFactor (362 : Fin 988) ≤ ((54526114184669 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_362
  obtain ⟨hpl, hph⟩ := kernel_bounds_2203
  obtain ⟨hcl, hch⟩ := kernel_bounds_2204
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2204
  have h : (((303601 / 128 : ℚ) : ℝ) * (logKernel ((2203 / 64 : ℚ) : ℝ) - logKernel ((551 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((551 / 16 : ℚ) : ℝ) + Real.log ((551 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((54526114184669 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_363 : ((255055038565163673 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2205 / 64 : ℚ) : ℝ) ∧
    Real.log ((2205 / 64 : ℚ) : ℝ) ≤ ((63763759641290919 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((255055038565163673 / 72057594037927936 : ℚ) : ℝ) ≤ ((2205 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2205 / 64 : ℚ) : ℝ) ≤ Real.exp ((63763759641290919 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_363 : heightPower (363 : Fin 988) ≤ ((411804907009641 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_363
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_363 : heightFactor (363 : Fin 988) ≤ ((53180751699043 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_363
  obtain ⟨hpl, hph⟩ := kernel_bounds_2204
  obtain ⟨hcl, hch⟩ := kernel_bounds_2205
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2205
  have h : (((4862025 / 2048 : ℚ) : ℝ) * (logKernel ((551 / 16 : ℚ) : ℝ) - logKernel ((2205 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2205 / 64 : ℚ) : ℝ) + Real.log ((2205 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((53180751699043 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_364 : ((63771927584531953 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((1103 / 32 : ℚ) : ℝ) ∧
    Real.log ((1103 / 32 : ℚ) : ℝ) ≤ ((255087710338127815 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((63771927584531953 / 18014398509481984 : ℚ) : ℝ) ≤ ((1103 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1103 / 32 : ℚ) : ℝ) ≤ Real.exp ((255087710338127815 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_364 : heightPower (364 : Fin 988) ≤ ((1651745298662809 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_364
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_364 : heightFactor (364 : Fin 988) ≤ ((25934279714321 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_364
  obtain ⟨hpl, hph⟩ := kernel_bounds_2205
  obtain ⟨hcl, hch⟩ := kernel_bounds_2206
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2206
  have h : (((1216609 / 512 : ℚ) : ℝ) * (logKernel ((2205 / 64 : ℚ) : ℝ) - logKernel ((1103 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1103 / 32 : ℚ) : ℝ) + Real.log ((1103 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((25934279714321 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_365 : ((63780091826008419 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((2207 / 64 : ℚ) : ℝ) ∧
    Real.log ((2207 / 64 : ℚ) : ℝ) ≤ ((255120367304033679 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((63780091826008419 / 18014398509481984 : ℚ) : ℝ) ≤ ((2207 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2207 / 64 : ℚ) : ℝ) ≤ Real.exp ((255120367304033679 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_365 : heightPower (365 : Fin 988) ≤ ((1656270911446983 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_365
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_365 : heightFactor (365 : Fin 988) ≤ ((50588720191023 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_365
  obtain ⟨hpl, hph⟩ := kernel_bounds_2206
  obtain ⟨hcl, hch⟩ := kernel_bounds_2207
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2207
  have h : (((4870849 / 2048 : ℚ) : ℝ) * (logKernel ((1103 / 32 : ℚ) : ℝ) - logKernel ((2207 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2207 / 64 : ℚ) : ℝ) + Real.log ((2207 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((50588720191023 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_366 : ((255153009476296495 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((69 / 2 : ℚ) : ℝ) ∧
    Real.log ((69 / 2 : ℚ) : ℝ) ≤ ((127576504738148249 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((255153009476296495 / 72057594037927936 : ℚ) : ℝ) ≤ ((69 / 2 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((69 / 2 : ℚ) : ℝ) ≤ Real.exp ((127576504738148249 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_366 : heightPower (366 : Fin 988) ≤ ((1660796466443489 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_366
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_366 : heightFactor (366 : Fin 988) ≤ ((12335109229897 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_366
  obtain ⟨hpl, hph⟩ := kernel_bounds_2207
  obtain ⟨hcl, hch⟩ := kernel_bounds_2208
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2208
  have h : (((4761 / 2 : ℚ) : ℝ) * (logKernel ((2207 / 64 : ℚ) : ℝ) - logKernel ((69 / 2 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((69 / 2 : ℚ) : ℝ) + Real.log ((69 / 2 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((12335109229897 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_367 : ((255185636868313275 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2209 / 64 : ℚ) : ℝ) ∧
    Real.log ((2209 / 64 : ℚ) : ℝ) ≤ ((127592818434156639 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((255185636868313275 / 72057594037927936 : ℚ) : ℝ) ≤ ((2209 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2209 / 64 : ℚ) : ℝ) ≤ Real.exp ((127592818434156639 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_367 : heightPower (367 : Fin 988) ≤ ((832660981852329 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_367
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_367 : heightFactor (367 : Fin 988) ≤ ((24061466084415 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_367
  obtain ⟨hpl, hph⟩ := kernel_bounds_2208
  obtain ⟨hcl, hch⟩ := kernel_bounds_2209
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2209
  have h : (((4879681 / 2048 : ℚ) : ℝ) * (logKernel ((69 / 2 : ℚ) : ℝ) - logKernel ((2209 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2209 / 64 : ℚ) : ℝ) + Real.log ((2209 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((24061466084415 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_368 : ((255218249493462831 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1105 / 32 : ℚ) : ℝ) ∧
    Real.log ((1105 / 32 : ℚ) : ℝ) ≤ ((127609124746731417 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((255218249493462831 / 72057594037927936 : ℚ) : ℝ) ≤ ((1105 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1105 / 32 : ℚ) : ℝ) ≤ Real.exp ((127609124746731417 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_368 : heightPower (368 : Fin 988) ≤ ((1669847403282753 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_368
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_368 : heightFactor (368 : Fin 988) ≤ ((23467723815867 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_368
  obtain ⟨hpl, hph⟩ := kernel_bounds_2209
  obtain ⟨hcl, hch⟩ := kernel_bounds_2210
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2210
  have h : (((1221025 / 512 : ℚ) : ℝ) * (logKernel ((2209 / 64 : ℚ) : ℝ) - logKernel ((1105 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1105 / 32 : ℚ) : ℝ) + Real.log ((1105 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((23467723815867 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_369 : ((255250847365105821 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2211 / 64 : ℚ) : ℝ) ∧
    Real.log ((2211 / 64 : ℚ) : ℝ) ≤ ((7976588980159557 / 2251799813685248 : ℚ) : ℝ) := by
  have hl : Real.exp ((255250847365105821 / 72057594037927936 : ℚ) : ℝ) ≤ ((2211 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2211 / 64 : ℚ) : ℝ) ≤ Real.exp ((7976588980159557 / 2251799813685248 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_369 : heightPower (369 : Fin 988) ≤ ((837186392614981 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_369
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_369 : heightFactor (369 : Fin 988) ≤ ((11444310917259 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_369
  obtain ⟨hpl, hph⟩ := kernel_bounds_2210
  obtain ⟨hcl, hch⟩ := kernel_bounds_2211
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2211
  have h : (((4888521 / 2048 : ℚ) : ℝ) * (logKernel ((1105 / 32 : ℚ) : ℝ) - logKernel ((2211 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2211 / 64 : ℚ) : ℝ) + Real.log ((2211 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((11444310917259 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_370 : ((255283430496584781 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((553 / 16 : ℚ) : ℝ) ∧
    Real.log ((553 / 16 : ℚ) : ℝ) ≤ ((15955214406036549 / 4503599627370496 : ℚ) : ℝ) := by
  have hl : Real.exp ((255283430496584781 / 72057594037927936 : ℚ) : ℝ) ≤ ((553 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((553 / 16 : ℚ) : ℝ) ≤ Real.exp ((15955214406036549 / 4503599627370496 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_370 : heightPower (370 : Fin 988) ≤ ((839449054799203 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_370
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_370 : heightFactor (370 : Fin 988) ≤ ((11161899712513 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_370
  obtain ⟨hpl, hph⟩ := kernel_bounds_2211
  obtain ⟨hcl, hch⟩ := kernel_bounds_2212
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2212
  have h : (((305809 / 128 : ℚ) : ℝ) * (logKernel ((2211 / 64 : ℚ) : ℝ) - logKernel ((553 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((553 / 16 : ℚ) : ℝ) + Real.log ((553 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((11161899712513 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_371 : ((255315998901224153 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2213 / 64 : ℚ) : ℝ) ∧
    Real.log ((2213 / 64 : ℚ) : ℝ) ≤ ((63828999725306039 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((255315998901224153 / 72057594037927936 : ℚ) : ℝ) ≤ ((2213 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2213 / 64 : ℚ) : ℝ) ≤ Real.exp ((63828999725306039 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_371 : heightPower (371 : Fin 988) ≤ ((420855844110033 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_371
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_371 : heightFactor (371 : Fin 988) ≤ ((43545809504793 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_371
  obtain ⟨hpl, hph⟩ := kernel_bounds_2212
  obtain ⟨hcl, hch⟩ := kernel_bounds_2213
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2213
  have h : (((4897369 / 2048 : ℚ) : ℝ) * (logKernel ((553 / 16 : ℚ) : ℝ) - logKernel ((2213 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2213 / 64 : ℚ) : ℝ) + Real.log ((2213 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((43545809504793 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_372 : ((15959284537020645 / 4503599627370496 : ℚ) : ℝ) ≤ Real.log ((1107 / 32 : ℚ) : ℝ) ∧
    Real.log ((1107 / 32 : ℚ) : ℝ) ≤ ((255348552592330323 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((15959284537020645 / 4503599627370496 : ℚ) : ℝ) ≤ ((1107 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1107 / 32 : ℚ) : ℝ) ≤ Real.exp ((255348552592330323 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_372 : heightPower (372 : Fin 988) ≤ ((105496786612945 / 17592186044416 : ℚ) : ℝ) := by
  have hh := log_height_bounds_372
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_372 : heightFactor (372 : Fin 988) ≤ ((42471189287081 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_372
  obtain ⟨hpl, hph⟩ := kernel_bounds_2213
  obtain ⟨hcl, hch⟩ := kernel_bounds_2214
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2214
  have h : (((1225449 / 512 : ℚ) : ℝ) * (logKernel ((2213 / 64 : ℚ) : ℝ) - logKernel ((1107 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1107 / 32 : ℚ) : ℝ) + Real.log ((1107 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((42471189287081 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_373 : ((255381091583191641 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2215 / 64 : ℚ) : ℝ) ∧
    Real.log ((2215 / 64 : ℚ) : ℝ) ≤ ((63845272895797911 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((255381091583191641 / 72057594037927936 : ℚ) : ℝ) ≤ ((2215 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2215 / 64 : ℚ) : ℝ) ≤ Real.exp ((63845272895797911 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_373 : heightPower (373 : Fin 988) ≤ ((423118434437819 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_373
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_373 : heightFactor (373 : Fin 988) ≤ ((20711534374207 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_373
  obtain ⟨hpl, hph⟩ := kernel_bounds_2214
  obtain ⟨hcl, hch⟩ := kernel_bounds_2215
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2215
  have h : (((4906225 / 2048 : ℚ) : ℝ) * (logKernel ((1107 / 32 : ℚ) : ℝ) - logKernel ((2215 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2215 / 64 : ℚ) : ℝ) + Real.log ((2215 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((20711534374207 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_374 : ((255413615887078479 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((277 / 8 : ℚ) : ℝ) ∧
    Real.log ((277 / 8 : ℚ) : ℝ) ≤ ((127706807943539241 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((255413615887078479 / 72057594037927936 : ℚ) : ℝ) ≤ ((277 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((277 / 8 : ℚ) : ℝ) ≤ Real.exp ((127706807943539241 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_374 : heightPower (374 : Fin 988) ≤ ((848499416162219 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_374
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_374 : heightFactor (374 : Fin 988) ≤ ((20200397461145 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_374
  obtain ⟨hpl, hph⟩ := kernel_bounds_2215
  obtain ⟨hcl, hch⟩ := kernel_bounds_2216
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2216
  have h : (((76729 / 32 : ℚ) : ℝ) * (logKernel ((2215 / 64 : ℚ) : ℝ) - logKernel ((277 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((277 / 8 : ℚ) : ℝ) + Real.log ((277 / 8 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((20200397461145 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_375 : ((255446125517243237 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2217 / 64 : ℚ) : ℝ) ∧
    Real.log ((2217 / 64 : ℚ) : ℝ) ≤ ((31930765689655405 / 9007199254740992 : ℚ) : ℝ) := by
  have hl : Real.exp ((255446125517243237 / 72057594037927936 : ℚ) : ℝ) ≤ ((2217 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2217 / 64 : ℚ) : ℝ) ≤ Real.exp ((31930765689655405 / 9007199254740992 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_375 : heightPower (375 : Fin 988) ≤ ((1701523869578373 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_375
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_375 : heightFactor (375 : Fin 988) ≤ ((9850932729689 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_375
  obtain ⟨hpl, hph⟩ := kernel_bounds_2216
  obtain ⟨hcl, hch⟩ := kernel_bounds_2217
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2217
  have h : (((4915089 / 2048 : ℚ) : ℝ) * (logKernel ((277 / 8 : ℚ) : ℝ) - logKernel ((2217 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2217 / 64 : ℚ) : ℝ) + Real.log ((2217 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((9850932729689 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_376 : ((255478620486920389 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1109 / 32 : ℚ) : ℝ) ∧
    Real.log ((1109 / 32 : ℚ) : ℝ) ≤ ((31934827560865049 / 9007199254740992 : ℚ) : ℝ) := by
  have hl : Real.exp ((255478620486920389 / 72057594037927936 : ℚ) : ℝ) ≤ ((1109 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1109 / 32 : ℚ) : ℝ) ≤ Real.exp ((31934827560865049 / 9007199254740992 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_376 : heightPower (376 : Fin 988) ≤ ((853024424782389 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_376
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_376 : heightFactor (376 : Fin 988) ≤ ((9607813882231 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_376
  obtain ⟨hpl, hph⟩ := kernel_bounds_2217
  obtain ⟨hcl, hch⟩ := kernel_bounds_2218
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2218
  have h : (((1229881 / 512 : ℚ) : ℝ) * (logKernel ((2217 / 64 : ℚ) : ℝ) - logKernel ((1109 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1109 / 32 : ℚ) : ℝ) + Real.log ((1109 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((9607813882231 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_377 : ((15969443800582907 / 4503599627370496 : ℚ) : ℝ) ≤ Real.log ((2219 / 64 : ℚ) : ℝ) ∧
    Real.log ((2219 / 64 : ℚ) : ℝ) ≤ ((255511100809326515 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((15969443800582907 / 4503599627370496 : ℚ) : ℝ) ≤ ((2219 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2219 / 64 : ℚ) : ℝ) ≤ Real.exp ((255511100809326515 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_377 : heightPower (377 : Fin 988) ≤ ((1710573772335281 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_377
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_377 : heightFactor (377 : Fin 988) ≤ ((1171336338725 / 8796093022208 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_377
  obtain ⟨hpl, hph⟩ := kernel_bounds_2218
  obtain ⟨hcl, hch⟩ := kernel_bounds_2219
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2219
  have h : (((4923961 / 2048 : ℚ) : ℝ) * (logKernel ((1109 / 32 : ℚ) : ℝ) - logKernel ((2219 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2219 / 64 : ℚ) : ℝ) + Real.log ((2219 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1171336338725 / 8796093022208 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_378 : ((255543566497660319 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((555 / 16 : ℚ) : ℝ) ∧
    Real.log ((555 / 16 : ℚ) : ℝ) ≤ ((127771783248830161 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((255543566497660319 / 72057594037927936 : ℚ) : ℝ) ≤ ((555 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((555 / 16 : ℚ) : ℝ) ≤ Real.exp ((127771783248830161 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_378 : heightPower (378 : Fin 988) ≤ ((1715098637941439 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_378
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_378 : heightFactor (378 : Fin 988) ≤ ((18278830927501 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_378
  obtain ⟨hpl, hph⟩ := kernel_bounds_2219
  obtain ⟨hcl, hch⟩ := kernel_bounds_2220
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2220
  have h : (((308025 / 128 : ℚ) : ℝ) * (logKernel ((2219 / 64 : ℚ) : ℝ) - logKernel ((555 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((555 / 16 : ℚ) : ℝ) + Real.log ((555 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((18278830927501 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_379 : ((255576017565102691 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2221 / 64 : ℚ) : ℝ) ∧
    Real.log ((2221 / 64 : ℚ) : ℝ) ≤ ((127788008782551347 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((255576017565102691 / 72057594037927936 : ℚ) : ℝ) ≤ ((2221 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2221 / 64 : ℚ) : ℝ) ≤ Real.exp ((127788008782551347 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_379 : heightPower (379 : Fin 988) ≤ ((429905861608685 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_379
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_379 : heightFactor (379 : Fin 988) ≤ ((35655376133723 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_379
  obtain ⟨hpl, hph⟩ := kernel_bounds_2220
  obtain ⟨hcl, hch⟩ := kernel_bounds_2221
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2221
  have h : (((4932841 / 2048 : ℚ) : ℝ) * (logKernel ((555 / 16 : ℚ) : ℝ) - logKernel ((2221 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2221 / 64 : ℚ) : ℝ) + Real.log ((2221 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((35655376133723 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_380 : ((255608454024816709 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1111 / 32 : ℚ) : ℝ) ∧
    Real.log ((1111 / 32 : ℚ) : ℝ) ≤ ((31951056753102089 / 9007199254740992 : ℚ) : ℝ) := by
  have hl : Real.exp ((255608454024816709 / 72057594037927936 : ℚ) : ℝ) ≤ ((1111 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1111 / 32 : ℚ) : ℝ) ≤ Real.exp ((31951056753102089 / 9007199254740992 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_380 : heightPower (380 : Fin 988) ≤ ((862074098933301 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_380
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_380 : heightFactor (380 : Fin 988) ≤ ((34775343426717 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_380
  obtain ⟨hpl, hph⟩ := kernel_bounds_2221
  obtain ⟨hcl, hch⟩ := kernel_bounds_2222
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2222
  have h : (((1234321 / 512 : ℚ) : ℝ) * (logKernel ((2221 / 64 : ℚ) : ℝ) - logKernel ((1111 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1111 / 32 : ℚ) : ℝ) + Real.log ((1111 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((34775343426717 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_381 : ((255640875889947685 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2223 / 64 : ℚ) : ℝ) ∧
    Real.log ((2223 / 64 : ℚ) : ℝ) ≤ ((31955109486243461 / 9007199254740992 : ℚ) : ℝ) := by
  have hl : Real.exp ((255640875889947685 / 72057594037927936 : ℚ) : ℝ) ≤ ((2223 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2223 / 64 : ℚ) : ℝ) ≤ Real.exp ((31955109486243461 / 9007199254740992 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_381 : heightPower (381 : Fin 988) ≤ ((864336446144187 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_381
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_381 : heightFactor (381 : Fin 988) ≤ ((33917015330087 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_381
  obtain ⟨hpl, hph⟩ := kernel_bounds_2222
  obtain ⟨hcl, hch⟩ := kernel_bounds_2223
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2223
  have h : (((4941729 / 2048 : ℚ) : ℝ) * (logKernel ((1111 / 32 : ℚ) : ℝ) - logKernel ((2223 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2223 / 64 : ℚ) : ℝ) + Real.log ((2223 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((33917015330087 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_382 : ((127836641586811599 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((139 / 4 : ℚ) : ℝ) ∧
    Real.log ((139 / 4 : ℚ) : ℝ) ≤ ((255673283173623201 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((127836641586811599 / 36028797018963968 : ℚ) : ℝ) ≤ ((139 / 4 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((139 / 4 : ℚ) : ℝ) ≤ Real.exp ((255673283173623201 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_382 : heightPower (382 : Fin 988) ≤ ((1733197529751335 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_382
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_382 : heightFactor (382 : Fin 988) ≤ ((33079856944053 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_382
  obtain ⟨hpl, hph⟩ := kernel_bounds_2223
  obtain ⟨hcl, hch⟩ := kernel_bounds_2224
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2224
  have h : (((19321 / 8 : ℚ) : ℝ) * (logKernel ((2223 / 64 : ℚ) : ℝ) - logKernel ((139 / 4 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((139 / 4 : ℚ) : ℝ) + Real.log ((139 / 4 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((33079856944053 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_383 : ((7990802371529785 / 2251799813685248 : ℚ) : ℝ) ≤ Real.log ((2225 / 64 : ℚ) : ℝ) ∧
    Real.log ((2225 / 64 : ℚ) : ℝ) ≤ ((255705675888953123 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((7990802371529785 / 2251799813685248 : ℚ) : ℝ) ≤ ((2225 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2225 / 64 : ℚ) : ℝ) ≤ Real.exp ((255705675888953123 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_383 : heightPower (383 : Fin 988) ≤ ((1737722110306697 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_383
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_383 : heightFactor (383 : Fin 988) ≤ ((32263346540701 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_383
  obtain ⟨hpl, hph⟩ := kernel_bounds_2224
  obtain ⟨hcl, hch⟩ := kernel_bounds_2225
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2225
  have h : (((4950625 / 2048 : ℚ) : ℝ) * (logKernel ((139 / 4 : ℚ) : ℝ) - logKernel ((2225 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2225 / 64 : ℚ) : ℝ) + Real.log ((2225 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((32263346540701 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

end LegendreK6.M2Pilot.Enclosures.Height011
