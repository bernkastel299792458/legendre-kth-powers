import LegendreK6.M2PilotDefinitions
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp

/-! Generated proposals: every bound is checked by Lean, not by trusting Arb. -/
namespace LegendreK6.M2Pilot.Enclosures.Height013
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem height_z_bounds_2257 : ((6722397383910917 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2257 / 64 : ℚ) : ℝ) ∧
    heightZ ((2257 / 64 : ℚ) : ℝ) ≤ ((13444794767821837 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((6722397383910917 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2257 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1043 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2257 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1043 / 192 : ℚ) : ℝ) ≤ ((13444794767821837 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2257 : ((5057628440961 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2257 / 64 : ℚ) : ℝ) ∧
    logKernel ((2257 / 64 : ℚ) : ℝ) ≤ ((2528814220483 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2257
  constructor
  · exact (show ((5057628440961 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((6722397383910917 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2257 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((13444794767821837 / 18446744073709551616 : ℚ) : ℝ) ≤ ((2528814220483 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2258 : ((13236352545189553 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1129 / 32 : ℚ) : ℝ) ∧
    heightZ ((1129 / 32 : ℚ) : ℝ) ≤ ((3309088136297389 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((13236352545189553 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1129 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-523 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1129 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-523 / 96 : ℚ) : ℝ) ≤ ((3309088136297389 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2258 : ((1225505393153 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((1129 / 32 : ℚ) : ℝ) ∧
    logKernel ((1129 / 32 : ℚ) : ℝ) ≤ ((4902021572617 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2258
  constructor
  · exact (show ((1225505393153 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((13236352545189553 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1129 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((3309088136297389 / 4611686018427387904 : ℚ) : ℝ) ≤ ((4902021572617 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2259 : ((1628892739960823 / 2305843009213693952 : ℚ) : ℝ) ≤ heightZ ((2259 / 64 : ℚ) : ℝ) ∧
    heightZ ((2259 / 64 : ℚ) : ℝ) ≤ ((13031141919686587 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((1628892739960823 / 2305843009213693952 : ℚ) : ℝ) ≤ Real.exp (-((2259 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1049 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2259 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1049 / 192 : ℚ) : ℝ) ≤ ((13031141919686587 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2259 : ((593900278037 / 9007199254740992 : ℚ) : ℝ) ≤ logKernel ((2259 / 64 : ℚ) : ℝ) ∧
    logKernel ((2259 / 64 : ℚ) : ℝ) ≤ ((4751202224301 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2259
  constructor
  · exact (show ((593900278037 / 9007199254740992 : ℚ) : ℝ) ≤ zKernel ((1628892739960823 / 2305843009213693952 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2259 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((13031141919686587 / 18446744073709551616 : ℚ) : ℝ) ≤ ((4751202224301 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2260 : ((3207278197510815 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((565 / 16 : ℚ) : ℝ) ∧
    heightZ ((565 / 16 : ℚ) : ℝ) ≤ ((12829112790043263 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((3207278197510815 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((565 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-263 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((565 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-263 / 48 : ℚ) : ℝ) ≤ ((12829112790043263 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2260 : ((4605023099505 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((565 / 16 : ℚ) : ℝ) ∧
    logKernel ((565 / 16 : ℚ) : ℝ) ≤ ((2302511549755 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2260
  constructor
  · exact (show ((4605023099505 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((3207278197510815 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((565 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((12829112790043263 / 18446744073709551616 : ℚ) : ℝ) ≤ ((2302511549755 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2261 : ((12630215831738103 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2261 / 64 : ℚ) : ℝ) ∧
    heightZ ((2261 / 64 : ℚ) : ℝ) ≤ ((6315107915869053 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((12630215831738103 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2261 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1055 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2261 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1055 / 192 : ℚ) : ℝ) ≤ ((6315107915869053 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2261 : ((1115835358393 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((2261 / 64 : ℚ) : ℝ) ∧
    logKernel ((2261 / 64 : ℚ) : ℝ) ≤ ((4463341433577 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2261
  constructor
  · exact (show ((1115835358393 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((12630215831738103 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2261 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((6315107915869053 / 9223372036854775808 : ℚ) : ℝ) ≤ ((4463341433577 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2262 : ((1554300310619433 / 2305843009213693952 : ℚ) : ℝ) ≤ heightZ ((1131 / 32 : ℚ) : ℝ) ∧
    heightZ ((1131 / 32 : ℚ) : ℝ) ≤ ((12434402484955467 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((1554300310619433 / 2305843009213693952 : ℚ) : ℝ) ≤ Real.exp (-((1131 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-529 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1131 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-529 / 96 : ℚ) : ℝ) ≤ ((12434402484955467 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2262 : ((4326018854233 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1131 / 32 : ℚ) : ℝ) ∧
    logKernel ((1131 / 32 : ℚ) : ℝ) ≤ ((2163009427119 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2262
  constructor
  · exact (show ((4326018854233 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((1554300310619433 / 2305843009213693952 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1131 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((12434402484955467 / 18446744073709551616 : ℚ) : ℝ) ≤ ((2163009427119 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2263 : ((6120812471364925 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2263 / 64 : ℚ) : ℝ) ∧
    heightZ ((2263 / 64 : ℚ) : ℝ) ≤ ((12241624942729853 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((6120812471364925 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2263 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1061 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2263 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1061 / 192 : ℚ) : ℝ) ≤ ((12241624942729853 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2263 : ((2096460623247 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2263 / 64 : ℚ) : ℝ) ∧
    logKernel ((2263 / 64 : ℚ) : ℝ) ≤ ((4192921246499 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2263
  constructor
  · exact (show ((2096460623247 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((6120812471364925 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2263 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((12241624942729853 / 18446744073709551616 : ℚ) : ℝ) ≤ ((4192921246499 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2264 : ((6025918069637037 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((283 / 8 : ℚ) : ℝ) ∧
    heightZ ((283 / 8 : ℚ) : ℝ) ≤ ((12051836139274077 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((6025918069637037 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((283 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-133 / 24 : ℚ) : ℝ) ∧
      Real.exp (-((283 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-133 / 24 : ℚ) : ℝ) ≤ ((12051836139274077 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2264 : ((1015979655411 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((283 / 8 : ℚ) : ℝ) ∧
    logKernel ((283 / 8 : ℚ) : ℝ) ≤ ((4063918621649 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2264
  constructor
  · exact (show ((1015979655411 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((6025918069637037 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((283 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((12051836139274077 / 18446744073709551616 : ℚ) : ℝ) ≤ ((4063918621649 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2265 : ((11864989738488343 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2265 / 64 : ℚ) : ℝ) ∧
    heightZ ((2265 / 64 : ℚ) : ℝ) ≤ ((5932494869244173 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((11864989738488343 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2265 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1067 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2265 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1067 / 192 : ℚ) : ℝ) ≤ ((5932494869244173 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2265 : ((123090155947 / 2251799813685248 : ℚ) : ℝ) ≤ logKernel ((2265 / 64 : ℚ) : ℝ) ∧
    logKernel ((2265 / 64 : ℚ) : ℝ) ≤ ((3938884990309 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2265
  constructor
  · exact (show ((123090155947 / 2251799813685248 : ℚ) : ℝ) ≤ zKernel ((11864989738488343 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2265 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((5932494869244173 / 9223372036854775808 : ℚ) : ℝ) ≤ ((3938884990309 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2266 : ((5840520061323753 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((1133 / 32 : ℚ) : ℝ) ∧
    heightZ ((1133 / 32 : ℚ) : ℝ) ≤ ((11681040122647509 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((5840520061323753 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((1133 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-535 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1133 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-535 / 96 : ℚ) : ℝ) ≤ ((11681040122647509 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2266 : ((3817698239383 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1133 / 32 : ℚ) : ℝ) ∧
    logKernel ((1133 / 32 : ℚ) : ℝ) ≤ ((954424559847 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2266
  constructor
  · exact (show ((3817698239383 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((5840520061323753 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1133 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((11681040122647509 / 18446744073709551616 : ℚ) : ℝ) ≤ ((954424559847 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2267 : ((11499942381263689 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2267 / 64 : ℚ) : ℝ) ∧
    heightZ ((2267 / 64 : ℚ) : ℝ) ≤ ((2874985595315923 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((11499942381263689 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2267 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1073 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2267 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1073 / 192 : ℚ) : ℝ) ≤ ((2874985595315923 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2267 : ((925060003203 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((2267 / 64 : ℚ) : ℝ) ∧
    logKernel ((2267 / 64 : ℚ) : ℝ) ≤ ((3700240012817 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2267
  constructor
  · exact (show ((925060003203 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((11499942381263689 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2267 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((2874985595315923 / 4611686018427387904 : ℚ) : ℝ) ≤ ((3700240012817 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2268 : ((11321652300121593 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((567 / 16 : ℚ) : ℝ) ∧
    heightZ ((567 / 16 : ℚ) : ℝ) ≤ ((2830413075030399 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((11321652300121593 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((567 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-269 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((567 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-269 / 48 : ℚ) : ℝ) ≤ ((2830413075030399 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2268 : ((896598898989 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((567 / 16 : ℚ) : ℝ) ∧
    logKernel ((567 / 16 : ℚ) : ℝ) ≤ ((3586395595961 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2268
  constructor
  · exact (show ((896598898989 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((11321652300121593 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((567 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((2830413075030399 / 4611686018427387904 : ℚ) : ℝ) ≤ ((3586395595961 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2269 : ((11146126350483795 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2269 / 64 : ℚ) : ℝ) ∧
    heightZ ((2269 / 64 : ℚ) : ℝ) ≤ ((5573063175241899 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((11146126350483795 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2269 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1079 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2269 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1079 / 192 : ℚ) : ℝ) ≤ ((5573063175241899 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2269 : ((869013450895 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((2269 / 64 : ℚ) : ℝ) ∧
    logKernel ((2269 / 64 : ℚ) : ℝ) ≤ ((3476053803585 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2269
  constructor
  · exact (show ((869013450895 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((11146126350483795 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2269 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((5573063175241899 / 9223372036854775808 : ℚ) : ℝ) ≤ ((3476053803585 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2270 : ((10973321678463393 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1135 / 32 : ℚ) : ℝ) ∧
    heightZ ((1135 / 32 : ℚ) : ℝ) ≤ ((2743330419615849 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((10973321678463393 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1135 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-541 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1135 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-541 / 96 : ℚ) : ℝ) ≤ ((2743330419615849 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2270 : ((1684553435629 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((1135 / 32 : ℚ) : ℝ) ∧
    logKernel ((1135 / 32 : ℚ) : ℝ) ≤ ((3369106871263 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2270
  constructor
  · exact (show ((1684553435629 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((10973321678463393 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1135 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((2743330419615849 / 4611686018427387904 : ℚ) : ℝ) ≤ ((3369106871263 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2271 : ((5401598047280709 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2271 / 64 : ℚ) : ℝ) ∧
    heightZ ((2271 / 64 : ℚ) : ℝ) ≤ ((10803196094561421 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((5401598047280709 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2271 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1085 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2271 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1085 / 192 : ℚ) : ℝ) ≤ ((10803196094561421 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2271 : ((1632725175063 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2271 / 64 : ℚ) : ℝ) ∧
    logKernel ((2271 / 64 : ℚ) : ℝ) ≤ ((3265450350131 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2271
  constructor
  · exact (show ((1632725175063 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((5401598047280709 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2271 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((10803196094561421 / 18446744073709551616 : ℚ) : ℝ) ≤ ((3265450350131 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2272 : ((10635708063366459 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((71 / 2 : ℚ) : ℝ) ∧
    heightZ ((71 / 2 : ℚ) : ℝ) ≤ ((5317854031683231 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((10635708063366459 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((71 / 2 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-17 / 3 : ℚ) : ℝ) ∧
      Real.exp (-((71 / 2 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-17 / 3 : ℚ) : ℝ) ≤ ((5317854031683231 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2272 : ((1582491502437 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((71 / 2 : ℚ) : ℝ) ∧
    logKernel ((71 / 2 : ℚ) : ℝ) ≤ ((3164983004879 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2272
  constructor
  · exact (show ((1582491502437 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((10635708063366459 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((71 / 2 : ℚ) : ℝ)) hh).trans
      (show zKernel ((5317854031683231 / 9223372036854775808 : ℚ) : ℝ) ≤ ((3164983004879 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2273 : ((10470816693413971 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2273 / 64 : ℚ) : ℝ) ∧
    heightZ ((2273 / 64 : ℚ) : ℝ) ≤ ((5235408346706987 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((10470816693413971 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2273 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1091 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2273 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1091 / 192 : ℚ) : ℝ) ≤ ((5235408346706987 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2273 : ((3067606714877 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2273 / 64 : ℚ) : ℝ) ∧
    logKernel ((2273 / 64 : ℚ) : ℝ) ≤ ((1533803357441 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2273
  constructor
  · exact (show ((3067606714877 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((10470816693413971 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2273 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((5235408346706987 / 9223372036854775808 : ℚ) : ℝ) ≤ ((1533803357441 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2274 : ((10308481727202807 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1137 / 32 : ℚ) : ℝ) ∧
    heightZ ((1137 / 32 : ℚ) : ℝ) ≤ ((5154240863601405 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((10308481727202807 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1137 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-547 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1137 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-547 / 96 : ℚ) : ℝ) ≤ ((5154240863601405 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2274 : ((2973226378361 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1137 / 32 : ℚ) : ℝ) ∧
    logKernel ((1137 / 32 : ℚ) : ℝ) ≤ ((1486613189183 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2274
  constructor
  · exact (show ((2973226378361 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((10308481727202807 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1137 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((5154240863601405 / 9223372036854775808 : ℚ) : ℝ) ≤ ((1486613189183 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2275 : ((10148663531366521 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2275 / 64 : ℚ) : ℝ) ∧
    heightZ ((2275 / 64 : ℚ) : ℝ) ≤ ((2537165882841631 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((10148663531366521 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2275 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1097 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2275 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1097 / 192 : ℚ) : ℝ) ≤ ((2537165882841631 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2275 : ((2881749819529 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2275 / 64 : ℚ) : ℝ) ∧
    logKernel ((2275 / 64 : ℚ) : ℝ) ≤ ((1440874909767 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2275
  constructor
  · exact (show ((2881749819529 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((10148663531366521 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2275 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((2537165882841631 / 4611686018427387904 : ℚ) : ℝ) ≤ ((1440874909767 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2276 : ((4995661543498533 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((569 / 16 : ℚ) : ℝ) ∧
    heightZ ((569 / 16 : ℚ) : ℝ) ≤ ((9991323086997069 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((4995661543498533 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((569 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-275 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((569 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-275 / 48 : ℚ) : ℝ) ≤ ((9991323086997069 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2276 : ((1396543849267 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((569 / 16 : ℚ) : ℝ) ∧
    logKernel ((569 / 16 : ℚ) : ℝ) ≤ ((2793087698539 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2276
  constructor
  · exact (show ((1396543849267 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((4995661543498533 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((569 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((9991323086997069 / 18446744073709551616 : ℚ) : ℝ) ≤ ((2793087698539 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2277 : ((4918210990059245 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2277 / 64 : ℚ) : ℝ) ∧
    heightZ ((2277 / 64 : ℚ) : ℝ) ≤ ((9836421980118493 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((4918210990059245 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2277 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1103 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2277 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1103 / 192 : ℚ) : ℝ) ≤ ((9836421980118493 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2277 : ((1353576712113 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2277 / 64 : ℚ) : ℝ) ∧
    logKernel ((2277 / 64 : ℚ) : ℝ) ≤ ((2707153424231 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2277
  constructor
  · exact (show ((1353576712113 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((4918210990059245 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2277 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((9836421980118493 / 18446744073709551616 : ℚ) : ℝ) ≤ ((2707153424231 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2278 : ((9683922392308337 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1139 / 32 : ℚ) : ℝ) ∧
    heightZ ((1139 / 32 : ℚ) : ℝ) ≤ ((2420980598077085 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((9683922392308337 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1139 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-553 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1139 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-553 / 96 : ℚ) : ℝ) ≤ ((2420980598077085 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2278 : ((1311931534793 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((1139 / 32 : ℚ) : ℝ) ∧
    logKernel ((1139 / 32 : ℚ) : ℝ) ≤ ((2623863069591 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2278
  constructor
  · exact (show ((1311931534793 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((9683922392308337 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1139 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((2420980598077085 / 4611686018427387904 : ℚ) : ℝ) ≤ ((2623863069591 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2279 : ((9533787091464449 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2279 / 64 : ℚ) : ℝ) ∧
    heightZ ((2279 / 64 : ℚ) : ℝ) ≤ ((2383446772866113 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((9533787091464449 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2279 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1109 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2279 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1109 / 192 : ℚ) : ℝ) ≤ ((2383446772866113 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2279 : ((1271567644879 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2279 / 64 : ℚ) : ℝ) ∧
    logKernel ((2279 / 64 : ℚ) : ℝ) ≤ ((2543135289763 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2279
  constructor
  · exact (show ((1271567644879 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((9533787091464449 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2279 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((2383446772866113 / 4611686018427387904 : ℚ) : ℝ) ≤ ((2543135289763 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2280 : ((4692989711357453 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((285 / 8 : ℚ) : ℝ) ∧
    heightZ ((285 / 8 : ℚ) : ℝ) ≤ ((9385979422714909 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((4692989711357453 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((285 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-139 / 24 : ℚ) : ℝ) ∧
      Real.exp (-((285 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-139 / 24 : ℚ) : ℝ) ≤ ((9385979422714909 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2280 : ((2464891242603 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((285 / 8 : ℚ) : ℝ) ∧
    logKernel ((285 / 8 : ℚ) : ℝ) ≤ ((154055702663 / 4503599627370496 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2280
  constructor
  · exact (show ((2464891242603 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((4692989711357453 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((285 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((9385979422714909 / 18446744073709551616 : ℚ) : ℝ) ≤ ((154055702663 / 4503599627370496 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2281 : ((9240463299468905 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2281 / 64 : ℚ) : ℝ) ∧
    heightZ ((2281 / 64 : ℚ) : ℝ) ≤ ((2310115824867227 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((9240463299468905 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2281 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1115 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2281 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1115 / 192 : ℚ) : ℝ) ≤ ((2310115824867227 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2281 : ((597263627925 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((2281 / 64 : ℚ) : ℝ) ∧
    logKernel ((2281 / 64 : ℚ) : ℝ) ≤ ((2389054511705 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2281
  constructor
  · exact (show ((597263627925 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((9240463299468905 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2281 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((2310115824867227 / 4611686018427387904 : ℚ) : ℝ) ≤ ((2389054511705 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2282 : ((9097203194606377 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1141 / 32 : ℚ) : ℝ) ∧
    heightZ ((1141 / 32 : ℚ) : ℝ) ≤ ((2274300798651595 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((9097203194606377 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1141 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-559 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1141 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-559 / 96 : ℚ) : ℝ) ≤ ((2274300798651595 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2282 : ((578887757929 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((1141 / 32 : ℚ) : ℝ) ∧
    logKernel ((1141 / 32 : ℚ) : ℝ) ≤ ((2315551031721 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2282
  constructor
  · exact (show ((578887757929 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((9097203194606377 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1141 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((2274300798651595 / 4611686018427387904 : ℚ) : ℝ) ≤ ((2315551031721 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2283 : ((8956164131804197 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2283 / 64 : ℚ) : ℝ) ∧
    heightZ ((2283 / 64 : ℚ) : ℝ) ≤ ((1119520516475525 / 2305843009213693952 : ℚ) : ℝ) := by
  have h : ((8956164131804197 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2283 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1121 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2283 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1121 / 192 : ℚ) : ℝ) ≤ ((1119520516475525 / 2305843009213693952 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2283 : ((2244309016065 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2283 / 64 : ℚ) : ℝ) ∧
    logKernel ((2283 / 64 : ℚ) : ℝ) ≤ ((1122154508035 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2283
  constructor
  · exact (show ((2244309016065 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((8956164131804197 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2283 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1119520516475525 / 2305843009213693952 : ℚ) : ℝ) ≤ ((1122154508035 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2284 : ((8817311676996869 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((571 / 16 : ℚ) : ℝ) ∧
    heightZ ((571 / 16 : ℚ) : ℝ) ≤ ((1102163959624609 / 2305843009213693952 : ℚ) : ℝ) := by
  have h : ((8817311676996869 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((571 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-281 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((571 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-281 / 48 : ℚ) : ℝ) ≤ ((1102163959624609 / 2305843009213693952 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2284 : ((2175258886805 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((571 / 16 : ℚ) : ℝ) ∧
    logKernel ((571 / 16 : ℚ) : ℝ) ≤ ((1087629443405 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2284
  constructor
  · exact (show ((2175258886805 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((8817311676996869 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((571 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1102163959624609 / 2305843009213693952 : ℚ) : ℝ) ≤ ((1087629443405 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2285 : ((135634561405775 / 288230376151711744 : ℚ) : ℝ) ≤ heightZ ((2285 / 64 : ℚ) : ℝ) ∧
    heightZ ((2285 / 64 : ℚ) : ℝ) ≤ ((8680611929969603 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((135634561405775 / 288230376151711744 : ℚ) : ℝ) ≤ Real.exp (-((2285 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1127 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2285 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1127 / 192 : ℚ) : ℝ) ≤ ((8680611929969603 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2285 : ((2108333206681 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2285 / 64 : ℚ) : ℝ) ∧
    logKernel ((2285 / 64 : ℚ) : ℝ) ≤ ((1054166603343 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2285
  constructor
  · exact (show ((2108333206681 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((135634561405775 / 288230376151711744 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2285 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((8680611929969603 / 18446744073709551616 : ℚ) : ℝ) ≤ ((1054166603343 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2286 : ((8546031516081713 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1143 / 32 : ℚ) : ℝ) ∧
    heightZ ((1143 / 32 : ℚ) : ℝ) ≤ ((2136507879020429 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((8546031516081713 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1143 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-565 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1143 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-565 / 96 : ℚ) : ℝ) ≤ ((2136507879020429 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2286 : ((2043466613265 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1143 / 32 : ℚ) : ℝ) ∧
    logKernel ((1143 / 32 : ℚ) : ℝ) ≤ ((1021733306635 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2286
  constructor
  · exact (show ((2043466613265 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((8546031516081713 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1143 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((2136507879020429 / 4611686018427387904 : ℚ) : ℝ) ≤ ((1021733306635 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2287 : ((8413537578118375 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2287 / 64 : ℚ) : ℝ) ∧
    heightZ ((2287 / 64 : ℚ) : ℝ) ≤ ((4206768789059189 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((8413537578118375 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2287 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1133 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2287 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1133 / 192 : ℚ) : ℝ) ≤ ((4206768789059189 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2287 : ((123787234695 / 4503599627370496 : ℚ) : ℝ) ≤ logKernel ((2287 / 64 : ℚ) : ℝ) ∧
    logKernel ((2287 / 64 : ℚ) : ℝ) ≤ ((1980595755125 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2287
  constructor
  · exact (show ((123787234695 / 4503599627370496 : ℚ) : ℝ) ≤ zKernel ((8413537578118375 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2287 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((4206768789059189 / 9223372036854775808 : ℚ) : ℝ) ≤ ((1980595755125 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2288 : ((8283097768268653 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((143 / 4 : ℚ) : ℝ) ∧
    heightZ ((143 / 4 : ℚ) : ℝ) ≤ ((517693610516791 / 1152921504606846976 : ℚ) : ℝ) := by
  have h : ((8283097768268653 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((143 / 4 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-71 / 12 : ℚ) : ℝ) ∧
      Real.exp (-((143 / 4 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-71 / 12 : ℚ) : ℝ) ≤ ((517693610516791 / 1152921504606846976 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2288 : ((1919659229925 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((143 / 4 : ℚ) : ℝ) ∧
    logKernel ((143 / 4 : ℚ) : ℝ) ≤ ((959829614965 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2288
  constructor
  · exact (show ((1919659229925 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((8283097768268653 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((143 / 4 : ℚ) : ℝ)) hh).trans
      (show zKernel ((517693610516791 / 1152921504606846976 : ℚ) : ℝ) ≤ ((959829614965 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

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

theorem log_height_bounds_416 : ((128383273713964857 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((1129 / 32 : ℚ) : ℝ) ∧
    Real.log ((1129 / 32 : ℚ) : ℝ) ≤ ((256766547427929717 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((128383273713964857 / 36028797018963968 : ℚ) : ℝ) ≤ ((1129 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1129 / 32 : ℚ) : ℝ) ≤ Real.exp ((256766547427929717 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_416 : heightPower (416 : Fin 988) ≤ ((117937604663891 / 17592186044416 : ℚ) : ℝ) := by
  have hh := log_height_bounds_416
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_416 : heightFactor (416 : Fin 988) ≤ ((3534652748949 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_416
  obtain ⟨hpl, hph⟩ := kernel_bounds_2257
  obtain ⟨hcl, hch⟩ := kernel_bounds_2258
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2258
  have h : (((1274641 / 512 : ℚ) : ℝ) * (logKernel ((2257 / 64 : ℚ) : ℝ) - logKernel ((1129 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1129 / 32 : ℚ) : ℝ) + Real.log ((1129 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((3534652748949 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_417 : ((256798452495547669 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2259 / 64 : ℚ) : ℝ) ∧
    Real.log ((2259 / 64 : ℚ) : ℝ) ≤ ((32099806561943459 / 9007199254740992 : ℚ) : ℝ) := by
  have hl : Real.exp ((256798452495547669 / 72057594037927936 : ℚ) : ℝ) ≤ ((2259 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2259 / 64 : ℚ) : ℝ) ≤ Real.exp ((32099806561943459 / 9007199254740992 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_417 : heightPower (417 : Fin 988) ≤ ((1891524350303743 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_417
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_417 : heightFactor (417 : Fin 988) ≤ ((13789409788611 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_417
  obtain ⟨hpl, hph⟩ := kernel_bounds_2258
  obtain ⟨hcl, hch⟩ := kernel_bounds_2259
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2259
  have h : (((5103081 / 2048 : ℚ) : ℝ) * (logKernel ((1129 / 32 : ℚ) : ℝ) - logKernel ((2259 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2259 / 64 : ℚ) : ℝ) + Real.log ((2259 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((13789409788611 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_418 : ((256830343442754621 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((565 / 16 : ℚ) : ℝ) ∧
    Real.log ((565 / 16 : ℚ) : ℝ) ≤ ((4012974116293041 / 1125899906842624 : ℚ) : ℝ) := by
  have hl : Real.exp ((256830343442754621 / 72057594037927936 : ℚ) : ℝ) ≤ ((565 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((565 / 16 : ℚ) : ℝ) ≤ Real.exp ((4012974116293041 / 1125899906842624 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_418 : heightPower (418 : Fin 988) ≤ ((948023485413687 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_418
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_418 : heightFactor (418 : Fin 988) ≤ ((6724413573305 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_418
  obtain ⟨hpl, hph⟩ := kernel_bounds_2259
  obtain ⟨hcl, hch⟩ := kernel_bounds_2260
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2260
  have h : (((319225 / 128 : ℚ) : ℝ) * (logKernel ((2259 / 64 : ℚ) : ℝ) - logKernel ((565 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((565 / 16 : ℚ) : ℝ) + Real.log ((565 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((6724413573305 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_419 : ((128431110141021873 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2261 / 64 : ℚ) : ℝ) ∧
    Real.log ((2261 / 64 : ℚ) : ℝ) ≤ ((256862220282043749 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((128431110141021873 / 36028797018963968 : ℚ) : ℝ) ≤ ((2261 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2261 / 64 : ℚ) : ℝ) ≤ Real.exp ((256862220282043749 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_419 : heightPower (419 : Fin 988) ≤ ((1900569536241951 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_419
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_419 : heightFactor (419 : Fin 988) ≤ ((13116650514009 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_419
  obtain ⟨hpl, hph⟩ := kernel_bounds_2260
  obtain ⟨hcl, hch⟩ := kernel_bounds_2261
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2261
  have h : (((5112121 / 2048 : ℚ) : ℝ) * (logKernel ((565 / 16 : ℚ) : ℝ) - logKernel ((2261 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2261 / 64 : ℚ) : ℝ) + Real.log ((2261 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((13116650514009 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_420 : ((256894083025891647 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1131 / 32 : ℚ) : ℝ) ∧
    Real.log ((1131 / 32 : ℚ) : ℝ) ≤ ((128447041512945825 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((256894083025891647 / 72057594037927936 : ℚ) : ℝ) ≤ ((1131 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1131 / 32 : ℚ) : ℝ) ≤ Real.exp ((128447041512945825 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_420 : heightPower (420 : Fin 988) ≤ ((1905092046596211 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_420
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_420 : heightFactor (420 : Fin 988) ≤ ((12792672573169 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_420
  obtain ⟨hpl, hph⟩ := kernel_bounds_2261
  obtain ⟨hcl, hch⟩ := kernel_bounds_2262
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2262
  have h : (((1279161 / 512 : ℚ) : ℝ) * (logKernel ((2261 / 64 : ℚ) : ℝ) - logKernel ((1131 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1131 / 32 : ℚ) : ℝ) + Real.log ((1131 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((12792672573169 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_421 : ((256925931686758383 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2263 / 64 : ℚ) : ℝ) ∧
    Real.log ((2263 / 64 : ℚ) : ℝ) ≤ ((128462965843379193 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((256925931686758383 / 72057594037927936 : ℚ) : ℝ) ≤ ((2263 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2263 / 64 : ℚ) : ℝ) ≤ Real.exp ((128462965843379193 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_421 : heightPower (421 : Fin 988) ≤ ((1909614501938825 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_421
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_421 : heightFactor (421 : Fin 988) ≤ ((12476691115613 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_421
  obtain ⟨hpl, hph⟩ := kernel_bounds_2262
  obtain ⟨hcl, hch⟩ := kernel_bounds_2263
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2263
  have h : (((5121169 / 2048 : ℚ) : ℝ) * (logKernel ((1131 / 32 : ℚ) : ℝ) - logKernel ((2263 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2263 / 64 : ℚ) : ℝ) + Real.log ((2263 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((12476691115613 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_422 : ((64239441569271875 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((283 / 8 : ℚ) : ℝ) ∧
    Real.log ((283 / 8 : ℚ) : ℝ) ≤ ((256957766277087503 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((64239441569271875 / 18014398509481984 : ℚ) : ℝ) ≤ ((283 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((283 / 8 : ℚ) : ℝ) ≤ Real.exp ((256957766277087503 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_422 : heightPower (422 : Fin 988) ≤ ((1914136902318403 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_422
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_422 : heightFactor (422 : Fin 988) ≤ ((6084254458105 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_422
  obtain ⟨hpl, hph⟩ := kernel_bounds_2263
  obtain ⟨hcl, hch⟩ := kernel_bounds_2264
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2264
  have h : (((80089 / 32 : ℚ) : ℝ) * (logKernel ((2263 / 64 : ℚ) : ℝ) - logKernel ((283 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((283 / 8 : ℚ) : ℝ) + Real.log ((283 / 8 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((6084254458105 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_423 : ((32123698351163257 / 9007199254740992 : ℚ) : ℝ) ≤ Real.log ((2265 / 64 : ℚ) : ℝ) ∧
    Real.log ((2265 / 64 : ℚ) : ℝ) ≤ ((256989586809306059 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((32123698351163257 / 9007199254740992 : ℚ) : ℝ) ≤ ((2265 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2265 / 64 : ℚ) : ℝ) ≤ Real.exp ((256989586809306059 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_423 : heightPower (423 : Fin 988) ≤ ((1918659247783485 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_423
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_423 : heightFactor (423 : Fin 988) ≤ ((11867933610465 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_423
  obtain ⟨hpl, hph⟩ := kernel_bounds_2264
  obtain ⟨hcl, hch⟩ := kernel_bounds_2265
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2265
  have h : (((5130225 / 2048 : ℚ) : ℝ) * (logKernel ((283 / 8 : ℚ) : ℝ) - logKernel ((2265 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2265 / 64 : ℚ) : ℝ) + Real.log ((2265 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((11867933610465 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_424 : ((257021393295824655 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1133 / 32 : ℚ) : ℝ) ∧
    Real.log ((1133 / 32 : ℚ) : ℝ) ≤ ((128510696647912329 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((257021393295824655 / 72057594037927936 : ℚ) : ℝ) ≤ ((1133 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1133 / 32 : ℚ) : ℝ) ≤ Real.exp ((128510696647912329 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_424 : heightPower (424 : Fin 988) ≤ ((1923181538382553 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_424
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_424 : heightFactor (424 : Fin 988) ≤ ((11574777574821 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_424
  obtain ⟨hpl, hph⟩ := kernel_bounds_2265
  obtain ⟨hcl, hch⟩ := kernel_bounds_2266
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2266
  have h : (((1283689 / 512 : ℚ) : ℝ) * (logKernel ((2265 / 64 : ℚ) : ℝ) - logKernel ((1133 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1133 / 32 : ℚ) : ℝ) + Real.log ((1133 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((11574777574821 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_425 : ((128526592874518737 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2267 / 64 : ℚ) : ℝ) ∧
    Real.log ((2267 / 64 : ℚ) : ℝ) ≤ ((257053185749037477 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((128526592874518737 / 36028797018963968 : ℚ) : ℝ) ≤ ((2267 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2267 / 64 : ℚ) : ℝ) ≤ Real.exp ((257053185749037477 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_425 : heightPower (425 : Fin 988) ≤ ((1927703774164019 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_425
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_425 : heightFactor (425 : Fin 988) ≤ ((5644428904955 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_425
  obtain ⟨hpl, hph⟩ := kernel_bounds_2266
  obtain ⟨hcl, hch⟩ := kernel_bounds_2267
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2267
  have h : (((5139289 / 2048 : ℚ) : ℝ) * (logKernel ((1133 / 32 : ℚ) : ℝ) - logKernel ((2267 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2267 / 64 : ℚ) : ℝ) + Real.log ((2267 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((5644428904955 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_426 : ((257084964181322291 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((567 / 16 : ℚ) : ℝ) ∧
    Real.log ((567 / 16 : ℚ) : ℝ) ≤ ((128542482090661147 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((257084964181322291 / 72057594037927936 : ℚ) : ℝ) ≤ ((567 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((567 / 16 : ℚ) : ℝ) ≤ Real.exp ((128542482090661147 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_426 : heightPower (426 : Fin 988) ≤ ((483056488794059 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_426
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_426 : heightFactor (426 : Fin 988) ≤ ((11009995826675 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_426
  obtain ⟨hpl, hph⟩ := kernel_bounds_2267
  obtain ⟨hcl, hch⟩ := kernel_bounds_2268
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2268
  have h : (((321489 / 128 : ℚ) : ℝ) * (logKernel ((2267 / 64 : ℚ) : ℝ) - logKernel ((567 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((567 / 16 : ℚ) : ℝ) + Real.log ((567 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((11009995826675 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_427 : ((64279182151260129 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((2269 / 64 : ℚ) : ℝ) ∧
    Real.log ((2269 / 64 : ℚ) : ℝ) ≤ ((257116728605040519 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((64279182151260129 / 18014398509481984 : ℚ) : ℝ) ≤ ((2269 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2269 / 64 : ℚ) : ℝ) ≤ Real.exp ((257116728605040519 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_427 : heightPower (427 : Fin 988) ≤ ((1936748081467489 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_427
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_427 : heightFactor (427 : Fin 988) ≤ ((10738017535291 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_427
  obtain ⟨hpl, hph⟩ := kernel_bounds_2268
  obtain ⟨hcl, hch⟩ := kernel_bounds_2269
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2269
  have h : (((5148361 / 2048 : ℚ) : ℝ) * (logKernel ((567 / 16 : ℚ) : ℝ) - logKernel ((2269 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2269 / 64 : ℚ) : ℝ) + Real.log ((2269 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((10738017535291 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_428 : ((128574239516268609 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((1135 / 32 : ℚ) : ℝ) ∧
    Real.log ((1135 / 32 : ℚ) : ℝ) ≤ ((257148479032537221 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((128574239516268609 / 36028797018963968 : ℚ) : ℝ) ≤ ((1135 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1135 / 32 : ℚ) : ℝ) ≤ Real.exp ((257148479032537221 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_428 : heightPower (428 : Fin 988) ≤ ((970635076543001 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_428
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_428 : heightFactor (428 : Fin 988) ≤ ((2618188284207 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_428
  obtain ⟨hpl, hph⟩ := kernel_bounds_2269
  obtain ⟨hcl, hch⟩ := kernel_bounds_2270
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2270
  have h : (((1288225 / 512 : ℚ) : ℝ) * (logKernel ((2269 / 64 : ℚ) : ℝ) - logKernel ((1135 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1135 / 32 : ℚ) : ℝ) + Real.log ((1135 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((2618188284207 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_429 : ((257180215476141155 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2271 / 64 : ℚ) : ℝ) ∧
    Real.log ((2271 / 64 : ℚ) : ℝ) ≤ ((128590107738070579 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((257180215476141155 / 72057594037927936 : ℚ) : ℝ) ≤ ((2271 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2271 / 64 : ℚ) : ℝ) ≤ Real.exp ((128590107738070579 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_429 : heightPower (429 : Fin 988) ≤ ((972896085039967 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_429
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_429 : heightFactor (429 : Fin 988) ≤ ((2553509254393 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_429
  obtain ⟨hpl, hph⟩ := kernel_bounds_2270
  obtain ⟨hcl, hch⟩ := kernel_bounds_2271
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2271
  have h : (((5157441 / 2048 : ℚ) : ℝ) * (logKernel ((1135 / 32 : ℚ) : ℝ) - logKernel ((2271 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2271 / 64 : ℚ) : ℝ) + Real.log ((2271 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((2553509254393 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_430 : ((128605968974082401 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((71 / 2 : ℚ) : ℝ) ∧
    Real.log ((71 / 2 : ℚ) : ℝ) ≤ ((257211937948164805 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((128605968974082401 / 36028797018963968 : ℚ) : ℝ) ≤ ((71 / 2 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((71 / 2 : ℚ) : ℝ) ≤ Real.exp ((257211937948164805 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_430 : heightPower (430 : Fin 988) ≤ ((487578533124345 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_430
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_430 : heightFactor (430 : Fin 988) ≤ ((9961707645947 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_430
  obtain ⟨hpl, hph⟩ := kernel_bounds_2271
  obtain ⟨hcl, hch⟩ := kernel_bounds_2272
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2272
  have h : (((5041 / 2 : ℚ) : ℝ) * (logKernel ((2271 / 64 : ℚ) : ℝ) - logKernel ((71 / 2 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((71 / 2 : ℚ) : ℝ) + Real.log ((71 / 2 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((9961707645947 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_431 : ((64310911615226095 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((2273 / 64 : ℚ) : ℝ) ∧
    Real.log ((2273 / 64 : ℚ) : ℝ) ≤ ((257243646460904383 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((64310911615226095 / 18014398509481984 : ℚ) : ℝ) ≤ ((2273 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2273 / 64 : ℚ) : ℝ) ≤ Real.exp ((257243646460904383 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_431 : heightPower (431 : Fin 988) ≤ ((1954836040386373 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_431
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_431 : heightFactor (431 : Fin 988) ≤ ((9715607471979 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_431
  obtain ⟨hpl, hph⟩ := kernel_bounds_2272
  obtain ⟨hcl, hch⟩ := kernel_bounds_2273
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2273
  have h : (((5166529 / 2048 : ℚ) : ℝ) * (logKernel ((71 / 2 : ℚ) : ℝ) - logKernel ((2273 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2273 / 64 : ℚ) : ℝ) + Real.log ((2273 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((9715607471979 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_432 : ((257275341026639883 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1137 / 32 : ℚ) : ℝ) ∧
    Real.log ((1137 / 32 : ℚ) : ℝ) ≤ ((128637670513319943 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((257275341026639883 / 72057594037927936 : ℚ) : ℝ) ≤ ((1137 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1137 / 32 : ℚ) : ℝ) ≤ Real.exp ((128637670513319943 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_432 : heightPower (432 : Fin 988) ≤ ((979678946897441 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_432
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_432 : heightFactor (432 : Fin 988) ≤ ((9475582829229 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_432
  obtain ⟨hpl, hph⟩ := kernel_bounds_2273
  obtain ⟨hcl, hch⟩ := kernel_bounds_2274
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2274
  have h : (((1292769 / 512 : ℚ) : ℝ) * (logKernel ((2273 / 64 : ℚ) : ℝ) - logKernel ((1137 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1137 / 32 : ℚ) : ℝ) + Real.log ((1137 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((9475582829229 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_433 : ((257307021657635111 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2275 / 64 : ℚ) : ℝ) ∧
    Real.log ((2275 / 64 : ℚ) : ℝ) ≤ ((128653510828817557 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((257307021657635111 / 72057594037927936 : ℚ) : ℝ) ≤ ((2275 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2275 / 64 : ℚ) : ℝ) ≤ Real.exp ((128653510828817557 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_433 : heightPower (433 : Fin 988) ≤ ((1963879692770811 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_433
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_433 : heightFactor (433 : Fin 988) ≤ ((9241483839141 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_433
  obtain ⟨hpl, hph⟩ := kernel_bounds_2274
  obtain ⟨hcl, hch⟩ := kernel_bounds_2275
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2275
  have h : (((5175625 / 2048 : ℚ) : ℝ) * (logKernel ((1137 / 32 : ℚ) : ℝ) - logKernel ((2275 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2275 / 64 : ℚ) : ℝ) + Real.log ((2275 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((9241483839141 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_434 : ((257338688366137693 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((569 / 16 : ℚ) : ℝ) ∧
    Real.log ((569 / 16 : ℚ) : ℝ) ≤ ((8041834011441803 / 2251799813685248 : ℚ) : ℝ) := by
  have hl : Real.exp ((257338688366137693 / 72057594037927936 : ℚ) : ℝ) ≤ ((569 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((569 / 16 : ℚ) : ℝ) ≤ Real.exp ((8041834011441803 / 2251799813685248 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_434 : heightPower (434 : Fin 988) ≤ ((1968401437362003 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_434
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_434 : heightFactor (434 : Fin 988) ≤ ((9013164317745 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_434
  obtain ⟨hpl, hph⟩ := kernel_bounds_2275
  obtain ⟨hcl, hch⟩ := kernel_bounds_2276
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2276
  have h : (((323761 / 128 : ℚ) : ℝ) * (logKernel ((2275 / 64 : ℚ) : ℝ) - logKernel ((569 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((569 / 16 : ℚ) : ℝ) + Real.log ((569 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((9013164317745 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_435 : ((16085646322773695 / 4503599627370496 : ℚ) : ℝ) ≤ Real.log ((2277 / 64 : ℚ) : ℝ) ∧
    Real.log ((2277 / 64 : ℚ) : ℝ) ≤ ((257370341164379123 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((16085646322773695 / 4503599627370496 : ℚ) : ℝ) ≤ ((2277 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2277 / 64 : ℚ) : ℝ) ≤ Real.exp ((257370341164379123 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_435 : heightPower (435 : Fin 988) ≤ ((1972923127616237 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_435
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_435 : heightFactor (435 : Fin 988) ≤ ((2197620421163 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_435
  obtain ⟨hpl, hph⟩ := kernel_bounds_2276
  obtain ⟨hcl, hch⟩ := kernel_bounds_2277
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2277
  have h : (((5184729 / 2048 : ℚ) : ℝ) * (logKernel ((569 / 16 : ℚ) : ℝ) - logKernel ((2277 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2277 / 64 : ℚ) : ℝ) + Real.log ((2277 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((2197620421163 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_436 : ((16087623754035923 / 4503599627370496 : ℚ) : ℝ) ≤ Real.log ((1139 / 32 : ℚ) : ℝ) ∧
    Real.log ((1139 / 32 : ℚ) : ℝ) ≤ ((257401980064574771 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((16087623754035923 / 4503599627370496 : ℚ) : ℝ) ≤ ((1139 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1139 / 32 : ℚ) : ℝ) ≤ Real.exp ((257401980064574771 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_436 : heightPower (436 : Fin 988) ≤ ((1977444763581231 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_436
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_436 : heightFactor (436 : Fin 988) ≤ ((4286648437149 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_436
  obtain ⟨hpl, hph⟩ := kernel_bounds_2277
  obtain ⟨hcl, hch⟩ := kernel_bounds_2278
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2278
  have h : (((1297321 / 512 : ℚ) : ℝ) * (logKernel ((2277 / 64 : ℚ) : ℝ) - logKernel ((1139 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1139 / 32 : ℚ) : ℝ) + Real.log ((1139 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((4286648437149 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_437 : ((128716802539461967 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2279 / 64 : ℚ) : ℝ) ∧
    Real.log ((2279 / 64 : ℚ) : ℝ) ≤ ((257433605078923937 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((128716802539461967 / 36028797018963968 : ℚ) : ℝ) ≤ ((2279 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2279 / 64 : ℚ) : ℝ) ≤ Real.exp ((257433605078923937 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_437 : heightPower (437 : Fin 988) ≤ ((495491586326159 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_437
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_437 : heightFactor (437 : Fin 988) ≤ ((522592140585 / 17592186044416 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_437
  obtain ⟨hpl, hph⟩ := kernel_bounds_2278
  obtain ⟨hcl, hch⟩ := kernel_bounds_2279
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2279
  have h : (((5193841 / 2048 : ℚ) : ℝ) * (logKernel ((1139 / 32 : ℚ) : ℝ) - logKernel ((2279 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2279 / 64 : ℚ) : ℝ) + Real.log ((2279 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((522592140585 / 17592186044416 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_438 : ((1005723500857851 / 281474976710656 : ℚ) : ℝ) ≤ Real.log ((285 / 8 : ℚ) : ℝ) ∧
    Real.log ((285 / 8 : ℚ) : ℝ) ≤ ((257465216219609859 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((1005723500857851 / 281474976710656 : ℚ) : ℝ) ≤ ((285 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((285 / 8 : ℚ) : ℝ) ≤ Real.exp ((257465216219609859 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_438 : heightPower (438 : Fin 988) ≤ ((1986487872834045 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_438
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_438 : heightFactor (438 : Fin 988) ≤ ((8154881516313 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_438
  obtain ⟨hpl, hph⟩ := kernel_bounds_2279
  obtain ⟨hcl, hch⟩ := kernel_bounds_2280
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2280
  have h : (((81225 / 32 : ℚ) : ℝ) * (logKernel ((2279 / 64 : ℚ) : ℝ) - logKernel ((285 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((285 / 8 : ℚ) : ℝ) + Real.log ((285 / 8 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((8154881516313 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_439 : ((257496813498799747 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2281 / 64 : ℚ) : ℝ) ∧
    Real.log ((2281 / 64 : ℚ) : ℝ) ≤ ((128748406749399875 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((257496813498799747 / 72057594037927936 : ℚ) : ℝ) ≤ ((2281 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2281 / 64 : ℚ) : ℝ) ≤ Real.exp ((128748406749399875 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_439 : heightPower (439 : Fin 988) ≤ ((248876168277123 / 35184372088832 : ℚ) : ℝ) := by
  have hh := log_height_bounds_439
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_439 : heightFactor (439 : Fin 988) ≤ ((1988347410765 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_439
  obtain ⟨hpl, hph⟩ := kernel_bounds_2280
  obtain ⟨hcl, hch⟩ := kernel_bounds_2281
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2281
  have h : (((5202961 / 2048 : ℚ) : ℝ) * (logKernel ((285 / 8 : ℚ) : ℝ) - logKernel ((2281 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2281 / 64 : ℚ) : ℝ) + Real.log ((2281 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1988347410765 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_440 : ((64382099232161205 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((1141 / 32 : ℚ) : ℝ) ∧
    Real.log ((1141 / 32 : ℚ) : ℝ) ≤ ((257528396928644823 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((64382099232161205 / 18014398509481984 : ℚ) : ℝ) ≤ ((1141 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1141 / 32 : ℚ) : ℝ) ≤ Real.exp ((257528396928644823 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_440 : heightPower (440 : Fin 988) ≤ ((249441345687615 / 35184372088832 : ℚ) : ℝ) := by
  have hh := log_height_bounds_440
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_440 : heightFactor (440 : Fin 988) ≤ ((7756872778593 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_440
  obtain ⟨hpl, hph⟩ := kernel_bounds_2281
  obtain ⟨hcl, hch⟩ := kernel_bounds_2282
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2282
  have h : (((1301881 / 512 : ℚ) : ℝ) * (logKernel ((2281 / 64 : ℚ) : ℝ) - logKernel ((1141 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1141 / 32 : ℚ) : ℝ) + Real.log ((1141 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((7756872778593 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_441 : ((257559966521280317 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2283 / 64 : ℚ) : ℝ) ∧
    Real.log ((2283 / 64 : ℚ) : ℝ) ≤ ((4024374476895005 / 1125899906842624 : ℚ) : ℝ) := by
  have hl : Real.exp ((257559966521280317 / 72057594037927936 : ℚ) : ℝ) ≤ ((2283 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2283 / 64 : ℚ) : ℝ) ≤ Real.exp ((4024374476895005 / 1125899906842624 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_441 : heightPower (441 : Fin 988) ≤ ((2000052130733257 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_441
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_441 : heightFactor (441 : Fin 988) ≤ ((7565208174625 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_441
  obtain ⟨hpl, hph⟩ := kernel_bounds_2282
  obtain ⟨hcl, hch⟩ := kernel_bounds_2283
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2283
  have h : (((5212089 / 2048 : ℚ) : ℝ) * (logKernel ((1141 / 32 : ℚ) : ℝ) - logKernel ((2283 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2283 / 64 : ℚ) : ℝ) + Real.log ((2283 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((7565208174625 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_442 : ((257591522288825539 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((571 / 16 : ℚ) : ℝ) ∧
    Real.log ((571 / 16 : ℚ) : ℝ) ≤ ((128795761144412771 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((257591522288825539 / 72057594037927936 : ℚ) : ℝ) ≤ ((571 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((571 / 16 : ℚ) : ℝ) ≤ Real.exp ((128795761144412771 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_442 : heightPower (442 : Fin 988) ≤ ((1002286720980667 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_442
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_442 : heightFactor (442 : Fin 988) ≤ ((7378276109163 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_442
  obtain ⟨hpl, hph⟩ := kernel_bounds_2283
  obtain ⟨hcl, hch⟩ := kernel_bounds_2284
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2284
  have h : (((326041 / 128 : ℚ) : ℝ) * (logKernel ((2283 / 64 : ℚ) : ℝ) - logKernel ((571 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((571 / 16 : ℚ) : ℝ) + Real.log ((571 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((7378276109163 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_443 : ((128811532121691935 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2285 / 64 : ℚ) : ℝ) ∧
    Real.log ((2285 / 64 : ℚ) : ℝ) ≤ ((257623064243383873 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((128811532121691935 / 36028797018963968 : ℚ) : ℝ) ≤ ((2285 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2285 / 64 : ℚ) : ℝ) ≤ Real.exp ((257623064243383873 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_443 : heightPower (443 : Fin 988) ≤ ((125568418702027 / 17592186044416 : ℚ) : ℝ) := by
  have hh := log_height_bounds_443
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_443 : heightFactor (443 : Fin 988) ≤ ((7195959811945 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_443
  obtain ⟨hpl, hph⟩ := kernel_bounds_2284
  obtain ⟨hcl, hch⟩ := kernel_bounds_2285
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2285
  have h : (((5221225 / 2048 : ℚ) : ℝ) * (logKernel ((571 / 16 : ℚ) : ℝ) - logKernel ((2285 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2285 / 64 : ℚ) : ℝ) + Real.log ((2285 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((7195959811945 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_444 : ((257654592397042807 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1143 / 32 : ℚ) : ℝ) ∧
    Real.log ((1143 / 32 : ℚ) : ℝ) ≤ ((128827296198521405 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((257654592397042807 / 72057594037927936 : ℚ) : ℝ) ≤ ((1143 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1143 / 32 : ℚ) : ℝ) ≤ Real.exp ((128827296198521405 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_444 : heightPower (444 : Fin 988) ≤ ((1006807951296883 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_444
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_444 : heightFactor (444 : Fin 988) ≤ ((7018145391731 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_444
  obtain ⟨hpl, hph⟩ := kernel_bounds_2285
  obtain ⟨hcl, hch⟩ := kernel_bounds_2286
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2286
  have h : (((1306449 / 512 : ℚ) : ℝ) * (logKernel ((2285 / 64 : ℚ) : ℝ) - logKernel ((1143 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1143 / 32 : ℚ) : ℝ) + Real.log ((1143 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((7018145391731 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_445 : ((257686106761873987 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2287 / 64 : ℚ) : ℝ) ∧
    Real.log ((2287 / 64 : ℚ) : ℝ) ≤ ((128843053380936995 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((257686106761873987 / 72057594037927936 : ℚ) : ℝ) ≤ ((2287 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2287 / 64 : ℚ) : ℝ) ≤ Real.exp ((128843053380936995 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_445 : heightPower (445 : Fin 988) ≤ ((504534263023123 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_445
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_445 : heightFactor (445 : Fin 988) ≤ ((3422360882685 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_445
  obtain ⟨hpl, hph⟩ := kernel_bounds_2286
  obtain ⟨hcl, hch⟩ := kernel_bounds_2287
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2287
  have h : (((5230369 / 2048 : ℚ) : ℝ) * (logKernel ((1143 / 32 : ℚ) : ℝ) - logKernel ((2287 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2287 / 64 : ℚ) : ℝ) + Real.log ((2287 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((3422360882685 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_446 : ((128858803674966609 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((143 / 4 : ℚ) : ℝ) ∧
    Real.log ((143 / 4 : ℚ) : ℝ) ≤ ((257717607349933221 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((128858803674966609 / 36028797018963968 : ℚ) : ℝ) ≤ ((143 / 4 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((143 / 4 : ℚ) : ℝ) ≤ Real.exp ((257717607349933221 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_446 : heightPower (446 : Fin 988) ≤ ((1011329073887851 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_446
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_446 : heightFactor (446 : Fin 988) ≤ ((6675580588619 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_446
  obtain ⟨hpl, hph⟩ := kernel_bounds_2287
  obtain ⟨hcl, hch⟩ := kernel_bounds_2288
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2288
  have h : (((20449 / 8 : ℚ) : ℝ) * (logKernel ((2287 / 64 : ℚ) : ℝ) - logKernel ((143 / 4 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((143 / 4 : ℚ) : ℝ) + Real.log ((143 / 4 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((6675580588619 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_447 : ((257749094173260501 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2289 / 64 : ℚ) : ℝ) ∧
    Real.log ((2289 / 64 : ℚ) : ℝ) ≤ ((32218636771657563 / 9007199254740992 : ℚ) : ℝ) := by
  have hl : Real.exp ((257749094173260501 / 72057594037927936 : ℚ) : ℝ) ≤ ((2289 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2289 / 64 : ℚ) : ℝ) ≤ Real.exp ((32218636771657563 / 9007199254740992 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_447 : heightPower (447 : Fin 988) ≤ ((506794797422607 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_447
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_447 : heightFactor (447 : Fin 988) ≤ ((6510616188663 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_447
  obtain ⟨hpl, hph⟩ := kernel_bounds_2288
  obtain ⟨hcl, hch⟩ := kernel_bounds_2289
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2289
  have h : (((5239521 / 2048 : ℚ) : ℝ) * (logKernel ((143 / 4 : ℚ) : ℝ) - logKernel ((2289 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2289 / 64 : ℚ) : ℝ) + Real.log ((2289 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((6510616188663 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

end LegendreK6.M2Pilot.Enclosures.Height013
