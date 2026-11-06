import LegendreK6.M2PilotDefinitions
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp

/-! Generated proposals: every bound is checked by Lean, not by trusting Arb. -/
namespace LegendreK6.M2Pilot.Enclosures.Height009
set_option maxRecDepth 100000
set_option maxHeartbeats 0

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

theorem height_z_bounds_2130 : ((12225518937703639 / 2305843009213693952 : ℚ) : ℝ) ≤ heightZ ((1065 / 32 : ℚ) : ℝ) ∧
    heightZ ((1065 / 32 : ℚ) : ℝ) ≤ ((97804151501629115 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((12225518937703639 / 2305843009213693952 : ℚ) : ℝ) ≤ Real.exp (-((1065 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-331 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1065 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-331 / 96 : ℚ) : ℝ) ≤ ((97804151501629115 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2130 : ((267641309287335 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1065 / 32 : ℚ) : ℝ) ∧
    logKernel ((1065 / 32 : ℚ) : ℝ) ≤ ((66910327321835 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2130
  constructor
  · exact (show ((267641309287335 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((12225518937703639 / 2305843009213693952 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1065 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((97804151501629115 / 18446744073709551616 : ℚ) : ℝ) ≤ ((66910327321835 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2131 : ((96287838677691025 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2131 / 64 : ℚ) : ℝ) ∧
    heightZ ((2131 / 64 : ℚ) : ℝ) ≤ ((24071959669422757 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((96287838677691025 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2131 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-665 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2131 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-665 / 192 : ℚ) : ℝ) ≤ ((24071959669422757 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2131 : ((259406851880047 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2131 / 64 : ℚ) : ℝ) ∧
    logKernel ((2131 / 64 : ℚ) : ℝ) ≤ ((64851712970013 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2131
  constructor
  · exact (show ((259406851880047 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((96287838677691025 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2131 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((24071959669422757 / 4611686018427387904 : ℚ) : ℝ) ≤ ((64851712970013 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2132 : ((94795034105138369 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((533 / 16 : ℚ) : ℝ) ∧
    heightZ ((533 / 16 : ℚ) : ℝ) ≤ ((23698758526284593 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((94795034105138369 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((533 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-167 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((533 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-167 / 48 : ℚ) : ℝ) ≤ ((23698758526284593 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2132 : ((7857054440407 / 2251799813685248 : ℚ) : ℝ) ≤ logKernel ((533 / 16 : ℚ) : ℝ) ∧
    logKernel ((533 / 16 : ℚ) : ℝ) ≤ ((251425742093029 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2132
  constructor
  · exact (show ((7857054440407 / 2251799813685248 : ℚ) : ℝ) ≤ zKernel ((94795034105138369 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((533 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((23698758526284593 / 4611686018427387904 : ℚ) : ℝ) ≤ ((251425742093029 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2133 : ((46662686661157449 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2133 / 64 : ℚ) : ℝ) ∧
    heightZ ((2133 / 64 : ℚ) : ℝ) ≤ ((93325373322314901 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((46662686661157449 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2133 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-671 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2133 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-671 / 192 : ℚ) : ℝ) ≤ ((93325373322314901 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2133 : ((243690185239437 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2133 / 64 : ℚ) : ℝ) ∧
    logKernel ((2133 / 64 : ℚ) : ℝ) ≤ ((121845092619721 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2133
  constructor
  · exact (show ((243690185239437 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((46662686661157449 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2133 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((93325373322314901 / 18446744073709551616 : ℚ) : ℝ) ≤ ((121845092619721 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2134 : ((91878497518018611 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1067 / 32 : ℚ) : ℝ) ∧
    heightZ ((1067 / 32 : ℚ) : ℝ) ≤ ((45939248759009307 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((91878497518018611 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1067 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-337 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1067 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-337 / 96 : ℚ) : ℝ) ≤ ((45939248759009307 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2134 : ((236192626449759 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1067 / 32 : ℚ) : ℝ) ∧
    logKernel ((1067 / 32 : ℚ) : ℝ) ≤ ((59048156612441 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2134
  constructor
  · exact (show ((236192626449759 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((91878497518018611 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1067 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((45939248759009307 / 9223372036854775808 : ℚ) : ℝ) ≤ ((59048156612441 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2135 : ((45227026721949791 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2135 / 64 : ℚ) : ℝ) ∧
    heightZ ((2135 / 64 : ℚ) : ℝ) ≤ ((90454053443899585 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((45227026721949791 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2135 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-677 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2135 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-677 / 192 : ℚ) : ℝ) ≤ ((90454053443899585 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2135 : ((114462871646681 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2135 / 64 : ℚ) : ℝ) ∧
    logKernel ((2135 / 64 : ℚ) : ℝ) ≤ ((228925743293367 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2135
  constructor
  · exact (show ((114462871646681 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((45227026721949791 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2135 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((90454053443899585 / 18446744073709551616 : ℚ) : ℝ) ≤ ((228925743293367 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2136 : ((44525846664107965 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((267 / 8 : ℚ) : ℝ) ∧
    heightZ ((267 / 8 : ℚ) : ℝ) ≤ ((89051693328215933 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((44525846664107965 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((267 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-85 / 24 : ℚ) : ℝ) ∧
      Real.exp (-((267 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-85 / 24 : ℚ) : ℝ) ≤ ((89051693328215933 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2136 : ((221882438627127 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((267 / 8 : ℚ) : ℝ) ∧
    logKernel ((267 / 8 : ℚ) : ℝ) ≤ ((55470609656783 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2136
  constructor
  · exact (show ((221882438627127 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((44525846664107965 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((267 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((89051693328215933 / 18446744073709551616 : ℚ) : ℝ) ≤ ((55470609656783 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2137 : ((43835537395463441 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2137 / 64 : ℚ) : ℝ) ∧
    heightZ ((2137 / 64 : ℚ) : ℝ) ≤ ((87671074790926885 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((43835537395463441 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2137 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-683 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2137 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-683 / 192 : ℚ) : ℝ) ≤ ((87671074790926885 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2137 : ((215055833664069 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2137 / 64 : ℚ) : ℝ) ∧
    logKernel ((2137 / 64 : ℚ) : ℝ) ≤ ((107527916832037 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2137
  constructor
  · exact (show ((215055833664069 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((43835537395463441 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2137 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((87671074790926885 / 18446744073709551616 : ℚ) : ℝ) ≤ ((107527916832037 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2138 : ((21577965190025549 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((1069 / 32 : ℚ) : ℝ) ∧
    heightZ ((1069 / 32 : ℚ) : ℝ) ≤ ((86311860760102199 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((21577965190025549 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((1069 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-343 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1069 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-343 / 96 : ℚ) : ℝ) ≤ ((86311860760102199 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2138 : ((3256863457113 / 1125899906842624 : ℚ) : ℝ) ≤ logKernel ((1069 / 32 : ℚ) : ℝ) ∧
    logKernel ((1069 / 32 : ℚ) : ℝ) ≤ ((208439261255237 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2138
  constructor
  · exact (show ((3256863457113 / 1125899906842624 : ℚ) : ℝ) ≤ zKernel ((21577965190025549 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1069 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((86311860760102199 / 18446744073709551616 : ℚ) : ℝ) ≤ ((208439261255237 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2139 : ((42486859694813767 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2139 / 64 : ℚ) : ℝ) ∧
    heightZ ((2139 / 64 : ℚ) : ℝ) ≤ ((84973719389627537 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((42486859694813767 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2139 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-689 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2139 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-689 / 192 : ℚ) : ℝ) ≤ ((84973719389627537 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2139 : ((50506564844567 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((2139 / 64 : ℚ) : ℝ) ∧
    logKernel ((2139 / 64 : ℚ) : ℝ) ≤ ((202026259378273 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2139
  constructor
  · exact (show ((50506564844567 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((42486859694813767 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2139 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((84973719389627537 / 18446744073709551616 : ℚ) : ℝ) ≤ ((202026259378273 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2140 : ((41828161989092847 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((535 / 16 : ℚ) : ℝ) ∧
    heightZ ((535 / 16 : ℚ) : ℝ) ≤ ((83656323978185697 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((41828161989092847 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((535 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-173 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((535 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-173 / 48 : ℚ) : ℝ) ≤ ((83656323978185697 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2140 : ((48952641206589 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((535 / 16 : ℚ) : ℝ) ∧
    logKernel ((535 / 16 : ℚ) : ℝ) ≤ ((195810564826361 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2140
  constructor
  · exact (show ((48952641206589 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((41828161989092847 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((535 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((83656323978185697 / 18446744073709551616 : ℚ) : ℝ) ≤ ((195810564826361 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2141 : ((82359352889493929 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2141 / 64 : ℚ) : ℝ) ∧
    heightZ ((2141 / 64 : ℚ) : ℝ) ≤ ((20589838222373483 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((82359352889493929 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2141 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-695 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2141 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-695 / 192 : ℚ) : ℝ) ≤ ((20589838222373483 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2141 : ((189786107091289 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2141 / 64 : ℚ) : ℝ) ∧
    logKernel ((2141 / 64 : ℚ) : ℝ) ≤ ((94893053545647 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2141
  constructor
  · exact (show ((189786107091289 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((82359352889493929 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2141 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((20589838222373483 / 4611686018427387904 : ℚ) : ℝ) ≤ ((94893053545647 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2142 : ((20270622368444465 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((1071 / 32 : ℚ) : ℝ) ∧
    heightZ ((1071 / 32 : ℚ) : ℝ) ≤ ((81082489473777863 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((20270622368444465 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((1071 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-349 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1071 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-349 / 96 : ℚ) : ℝ) ≤ ((81082489473777863 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2142 : ((183947002434763 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1071 / 32 : ℚ) : ℝ) ∧
    logKernel ((1071 / 32 : ℚ) : ℝ) ≤ ((11496687652173 / 4503599627370496 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2142
  constructor
  · exact (show ((183947002434763 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((20270622368444465 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1071 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((81082489473777863 / 18446744073709551616 : ℚ) : ℝ) ≤ ((11496687652173 / 4503599627370496 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2143 : ((79825421990462835 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2143 / 64 : ℚ) : ℝ) ∧
    heightZ ((2143 / 64 : ℚ) : ℝ) ≤ ((39912710995231419 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((79825421990462835 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2143 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-701 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2143 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-701 / 192 : ℚ) : ℝ) ≤ ((39912710995231419 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2143 : ((89143774071037 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2143 / 64 : ℚ) : ℝ) ∧
    logKernel ((2143 / 64 : ℚ) : ℝ) ≤ ((178287548142079 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2143
  constructor
  · exact (show ((89143774071037 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((79825421990462835 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2143 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((39912710995231419 / 9223372036854775808 : ℚ) : ℝ) ≤ ((178287548142079 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2144 : ((39293921766031919 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((67 / 2 : ℚ) : ℝ) ∧
    heightZ ((67 / 2 : ℚ) : ℝ) ≤ ((78587843532063841 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((39293921766031919 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((67 / 2 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-11 / 3 : ℚ) : ℝ) ∧
      Real.exp (-((67 / 2 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-11 / 3 : ℚ) : ℝ) ≤ ((78587843532063841 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2144 : ((172802216952599 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((67 / 2 : ℚ) : ℝ) ∧
    logKernel ((67 / 2 : ℚ) : ℝ) ≤ ((43200554238151 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2144
  constructor
  · exact (show ((172802216952599 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((39293921766031919 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((67 / 2 : ℚ) : ℝ)) hh).trans
      (show zKernel ((78587843532063841 / 18446744073709551616 : ℚ) : ℝ) ≤ ((43200554238151 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2145 : ((38684725974627689 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2145 / 64 : ℚ) : ℝ) ∧
    heightZ ((2145 / 64 : ℚ) : ℝ) ≤ ((77369451949255381 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((38684725974627689 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2145 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-707 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2145 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-707 / 192 : ℚ) : ℝ) ≤ ((77369451949255381 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2145 : ((83742825830825 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2145 / 64 : ℚ) : ℝ) ∧
    logKernel ((2145 / 64 : ℚ) : ℝ) ≤ ((167485651661655 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2145
  constructor
  · exact (show ((83742825830825 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((38684725974627689 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2145 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((77369451949255381 / 18446744073709551616 : ℚ) : ℝ) ≤ ((167485651661655 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2146 : ((38084974888551535 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((1073 / 32 : ℚ) : ℝ) ∧
    heightZ ((1073 / 32 : ℚ) : ℝ) ≤ ((76169949777103073 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((38084974888551535 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((1073 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-355 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1073 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-355 / 96 : ℚ) : ℝ) ≤ ((76169949777103073 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2146 : ((162332659888399 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1073 / 32 : ℚ) : ℝ) ∧
    logKernel ((1073 / 32 : ℚ) : ℝ) ≤ ((40583164972101 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2146
  constructor
  · exact (show ((162332659888399 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((38084974888551535 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1073 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((76169949777103073 / 18446744073709551616 : ℚ) : ℝ) ≤ ((40583164972101 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2147 : ((74989044162438875 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2147 / 64 : ℚ) : ℝ) ∧
    heightZ ((2147 / 64 : ℚ) : ℝ) ≤ ((37494522081219439 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((74989044162438875 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2147 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-713 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2147 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-713 / 192 : ℚ) : ℝ) ≤ ((37494522081219439 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2147 : ((78669104502391 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2147 / 64 : ℚ) : ℝ) ∧
    logKernel ((2147 / 64 : ℚ) : ℝ) ≤ ((157338209004787 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2147
  constructor
  · exact (show ((78669104502391 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((74989044162438875 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2147 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((37494522081219439 / 9223372036854775808 : ℚ) : ℝ) ≤ ((157338209004787 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2148 : ((73826446792362293 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((537 / 16 : ℚ) : ℝ) ∧
    heightZ ((537 / 16 : ℚ) : ℝ) ≤ ((9228305849045287 / 2305843009213693952 : ℚ) : ℝ) := by
  have h : ((73826446792362293 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((537 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-179 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((537 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-179 / 48 : ℚ) : ℝ) ≤ ((9228305849045287 / 2305843009213693952 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2148 : ((152497421220419 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((537 / 16 : ℚ) : ℝ) ∧
    logKernel ((537 / 16 : ℚ) : ℝ) ≤ ((19062177652553 / 9007199254740992 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2148
  constructor
  · exact (show ((152497421220419 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((73826446792362293 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((537 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((9228305849045287 / 2305843009213693952 : ℚ) : ℝ) ≤ ((19062177652553 / 9007199254740992 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2149 : ((72681873823850039 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2149 / 64 : ℚ) : ℝ) ∧
    heightZ ((2149 / 64 : ℚ) : ℝ) ≤ ((36340936911925021 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((72681873823850039 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2149 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-719 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2149 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-719 / 192 : ℚ) : ℝ) ≤ ((36340936911925021 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2149 : ((9237848051173 / 4503599627370496 : ℚ) : ℝ) ≤ logKernel ((2149 / 64 : ℚ) : ℝ) ∧
    logKernel ((2149 / 64 : ℚ) : ℝ) ≤ ((147805568818773 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2149
  constructor
  · exact (show ((9237848051173 / 4503599627370496 : ℚ) : ℝ) ≤ zKernel ((72681873823850039 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2149 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((36340936911925021 / 9223372036854775808 : ℚ) : ℝ) ≤ ((147805568818773 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2150 : ((35777522907228511 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((1075 / 32 : ℚ) : ℝ) ∧
    heightZ ((1075 / 32 : ℚ) : ℝ) ≤ ((71555045814457025 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((35777522907228511 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((1075 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-361 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1075 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-361 / 96 : ℚ) : ℝ) ≤ ((71555045814457025 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2150 : ((143258069539831 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1075 / 32 : ℚ) : ℝ) ∧
    logKernel ((1075 / 32 : ℚ) : ℝ) ≤ ((35814517384959 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2150
  constructor
  · exact (show ((143258069539831 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((35777522907228511 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1075 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((71555045814457025 / 18446744073709551616 : ℚ) : ℝ) ≤ ((35814517384959 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2151 : ((17611421913522925 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((2151 / 64 : ℚ) : ℝ) ∧
    heightZ ((2151 / 64 : ℚ) : ℝ) ≤ ((70445687654091703 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((17611421913522925 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((2151 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-725 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2151 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-725 / 192 : ℚ) : ℝ) ≤ ((70445687654091703 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2151 : ((138850482104927 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2151 / 64 : ℚ) : ℝ) ∧
    logKernel ((2151 / 64 : ℚ) : ℝ) ≤ ((34712620526233 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2151
  constructor
  · exact (show ((138850482104927 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((17611421913522925 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2151 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((70445687654091703 / 18446744073709551616 : ℚ) : ℝ) ≤ ((34712620526233 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2152 : ((34676764248924583 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((269 / 8 : ℚ) : ℝ) ∧
    heightZ ((269 / 8 : ℚ) : ℝ) ≤ ((69353528497849169 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((34676764248924583 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((269 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-91 / 24 : ℚ) : ℝ) ∧
      Real.exp (-((269 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-91 / 24 : ℚ) : ℝ) ≤ ((69353528497849169 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2152 : ((67289250939579 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((269 / 8 : ℚ) : ℝ) ∧
    logKernel ((269 / 8 : ℚ) : ℝ) ≤ ((134578501879163 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2152
  constructor
  · exact (show ((67289250939579 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((34676764248924583 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((269 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((69353528497849169 / 18446744073709551616 : ℚ) : ℝ) ≤ ((134578501879163 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2153 : ((34139150849942779 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2153 / 64 : ℚ) : ℝ) ∧
    heightZ ((2153 / 64 : ℚ) : ℝ) ≤ ((68278301699885561 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((34139150849942779 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2153 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-731 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2153 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-731 / 192 : ℚ) : ℝ) ≤ ((68278301699885561 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2153 : ((130437956667317 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2153 / 64 : ℚ) : ℝ) ∧
    logKernel ((2153 / 64 : ℚ) : ℝ) ≤ ((65218978333661 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2153
  constructor
  · exact (show ((130437956667317 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((34139150849942779 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2153 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((68278301699885561 / 18446744073709551616 : ℚ) : ℝ) ≤ ((65218978333661 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2154 : ((16804936187079413 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((1077 / 32 : ℚ) : ℝ) ∧
    heightZ ((1077 / 32 : ℚ) : ℝ) ≤ ((67219744748317655 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((16804936187079413 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((1077 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-367 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1077 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-367 / 96 : ℚ) : ℝ) ≤ ((67219744748317655 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2154 : ((126424802639149 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1077 / 32 : ℚ) : ℝ) ∧
    logKernel ((1077 / 32 : ℚ) : ℝ) ≤ ((63212401319577 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2154
  constructor
  · exact (show ((126424802639149 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((16804936187079413 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1077 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((67219744748317655 / 18446744073709551616 : ℚ) : ℝ) ≤ ((63212401319577 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2155 : ((33088799600565871 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2155 / 64 : ℚ) : ℝ) ∧
    heightZ ((2155 / 64 : ℚ) : ℝ) ≤ ((66177599201131745 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((33088799600565871 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2155 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-737 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2155 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-737 / 192 : ℚ) : ℝ) ≤ ((66177599201131745 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2155 : ((15316890047497 / 9007199254740992 : ℚ) : ℝ) ≤ logKernel ((2155 / 64 : ℚ) : ℝ) ∧
    logKernel ((2155 / 64 : ℚ) : ℝ) ≤ ((122535120379981 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2155
  constructor
  · exact (show ((15316890047497 / 9007199254740992 : ℚ) : ℝ) ≤ zKernel ((33088799600565871 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2155 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((66177599201131745 / 18446744073709551616 : ℚ) : ℝ) ≤ ((122535120379981 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2156 : ((32575805311543081 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((539 / 16 : ℚ) : ℝ) ∧
    heightZ ((539 / 16 : ℚ) : ℝ) ≤ ((65151610623086165 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((32575805311543081 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((539 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-185 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((539 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-185 / 48 : ℚ) : ℝ) ≤ ((65151610623086165 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2156 : ((7422819441427 / 4503599627370496 : ℚ) : ℝ) ≤ logKernel ((539 / 16 : ℚ) : ℝ) ∧
    logKernel ((539 / 16 : ℚ) : ℝ) ≤ ((118765111062837 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2156
  constructor
  · exact (show ((7422819441427 / 4503599627370496 : ℚ) : ℝ) ≤ zKernel ((32575805311543081 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((539 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((65151610623086165 / 18446744073709551616 : ℚ) : ℝ) ≤ ((118765111062837 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2157 : ((64141528523592043 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2157 / 64 : ℚ) : ℝ) ∧
    heightZ ((2157 / 64 : ℚ) : ℝ) ≤ ((32070764261796023 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((64141528523592043 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2157 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-743 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2157 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-743 / 192 : ℚ) : ℝ) ≤ ((32070764261796023 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2157 : ((115111092738371 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2157 / 64 : ℚ) : ℝ) ∧
    logKernel ((2157 / 64 : ℚ) : ℝ) ≤ ((14388886592297 / 9007199254740992 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2157
  constructor
  · exact (show ((115111092738371 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((64141528523592043 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2157 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((32070764261796023 / 9223372036854775808 : ℚ) : ℝ) ≤ ((14388886592297 / 9007199254740992 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2158 : ((15786776573889285 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((1079 / 32 : ℚ) : ℝ) ∧
    heightZ ((1079 / 32 : ℚ) : ℝ) ≤ ((63147106295557143 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((15786776573889285 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((1079 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-373 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1079 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-373 / 96 : ℚ) : ℝ) ≤ ((63147106295557143 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2158 : ((111569496738917 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1079 / 32 : ℚ) : ℝ) ∧
    logKernel ((1079 / 32 : ℚ) : ℝ) ≤ ((55784748369461 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2158
  constructor
  · exact (show ((111569496738917 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((15786776573889285 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1079 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((63147106295557143 / 18446744073709551616 : ℚ) : ℝ) ≤ ((55784748369461 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2159 : ((31084050577588899 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2159 / 64 : ℚ) : ℝ) ∧
    heightZ ((2159 / 64 : ℚ) : ℝ) ≤ ((62168101155177801 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((31084050577588899 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2159 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-749 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2159 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-749 / 192 : ℚ) : ℝ) ≤ ((62168101155177801 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2159 : ((108136864193159 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2159 / 64 : ℚ) : ℝ) ∧
    logKernel ((2159 / 64 : ℚ) : ℝ) ≤ ((27034216048291 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2159
  constructor
  · exact (show ((108136864193159 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((31084050577588899 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2159 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((62168101155177801 / 18446744073709551616 : ℚ) : ℝ) ≤ ((27034216048291 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2160 : ((61204274082664357 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((135 / 4 : ℚ) : ℝ) ∧
    heightZ ((135 / 4 : ℚ) : ℝ) ≤ ((7650534260333045 / 2305843009213693952 : ℚ) : ℝ) := by
  have h : ((61204274082664357 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((135 / 4 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-47 / 12 : ℚ) : ℝ) ∧
      Real.exp (-((135 / 4 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-47 / 12 : ℚ) : ℝ) ≤ ((7650534260333045 / 2305843009213693952 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2160 : ((102353361961 / 70368744177664 : ℚ) : ℝ) ≤ logKernel ((135 / 4 : ℚ) : ℝ) ∧
    logKernel ((135 / 4 : ℚ) : ℝ) ≤ ((104809842648069 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2160
  constructor
  · exact (show ((102353361961 / 70368744177664 : ℚ) : ℝ) ≤ zKernel ((61204274082664357 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((135 / 4 : ℚ) : ℝ)) hh).trans
      (show zKernel ((7650534260333045 / 2305843009213693952 : ℚ) : ℝ) ≤ ((104809842648069 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2161 : ((3765961860242845 / 1152921504606846976 : ℚ) : ℝ) ≤ heightZ ((2161 / 64 : ℚ) : ℝ) ∧
    heightZ ((2161 / 64 : ℚ) : ℝ) ≤ ((60255389763885523 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((3765961860242845 / 1152921504606846976 : ℚ) : ℝ) ≤ Real.exp (-((2161 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-755 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2161 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-755 / 192 : ℚ) : ℝ) ≤ ((60255389763885523 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2161 : ((25396295698685 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((2161 / 64 : ℚ) : ℝ) ∧
    logKernel ((2161 / 64 : ℚ) : ℝ) ≤ ((101585182794745 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2161
  constructor
  · exact (show ((25396295698685 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((3765961860242845 / 1152921504606846976 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2161 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((60255389763885523 / 18446744073709551616 : ℚ) : ℝ) ≤ ((101585182794745 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem log_height_bounds_288 : ((63140361848056367 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((1065 / 32 : ℚ) : ℝ) ∧
    Real.log ((1065 / 32 : ℚ) : ℝ) ≤ ((252561447392225471 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((63140361848056367 / 18014398509481984 : ℚ) : ℝ) ≤ ((1065 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1065 / 32 : ℚ) : ℝ) ≤ Real.exp ((252561447392225471 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_288 : heightPower (288 : Fin 988) ≤ ((653812774593237 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_288
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_288 : heightFactor (288 : Fin 988) ≤ ((345874255267161 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_288
  obtain ⟨hpl, hph⟩ := kernel_bounds_2129
  obtain ⟨hcl, hch⟩ := kernel_bounds_2130
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2130
  have h : (((1134225 / 512 : ℚ) : ℝ) * (logKernel ((2129 / 64 : ℚ) : ℝ) - logKernel ((1065 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1065 / 32 : ℚ) : ℝ) + Real.log ((1065 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((345874255267161 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_289 : ((252595269309785127 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2131 / 64 : ℚ) : ℝ) ∧
    Real.log ((2131 / 64 : ℚ) : ℝ) ≤ ((126297634654892565 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((252595269309785127 / 72057594037927936 : ℚ) : ℝ) ≤ ((2131 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2131 / 64 : ℚ) : ℝ) ≤ Real.exp ((126297634654892565 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_289 : heightPower (289 : Fin 988) ≤ ((656077856281523 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_289
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_289 : heightFactor (289 : Fin 988) ≤ ((168676325077749 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_289
  obtain ⟨hpl, hph⟩ := kernel_bounds_2130
  obtain ⟨hcl, hch⟩ := kernel_bounds_2131
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2131
  have h : (((4541161 / 2048 : ℚ) : ℝ) * (logKernel ((1065 / 32 : ℚ) : ℝ) - logKernel ((2131 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2131 / 64 : ℚ) : ℝ) + Real.log ((2131 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((168676325077749 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_290 : ((252629075359684077 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((533 / 16 : ℚ) : ℝ) ∧
    Real.log ((533 / 16 : ℚ) : ℝ) ≤ ((15789317209980255 / 4503599627370496 : ℚ) : ℝ) := by
  have hl : Real.exp ((252629075359684077 / 72057594037927936 : ℚ) : ℝ) ≤ ((533 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((533 / 16 : ℚ) : ℝ) ≤ Real.exp ((15789317209980255 / 4503599627370496 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_290 : heightPower (290 : Fin 988) ≤ ((1316685813956567 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_290
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_290 : heightFactor (290 : Fin 988) ≤ ((164520415089855 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_290
  obtain ⟨hpl, hph⟩ := kernel_bounds_2131
  obtain ⟨hcl, hch⟩ := kernel_bounds_2132
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2132
  have h : (((284089 / 128 : ℚ) : ℝ) * (logKernel ((2131 / 64 : ℚ) : ℝ) - logKernel ((533 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((533 / 16 : ℚ) : ℝ) + Real.log ((533 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((164520415089855 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_291 : ((252662865556804065 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2133 / 64 : ℚ) : ℝ) ∧
    Real.log ((2133 / 64 : ℚ) : ℝ) ≤ ((63165716389201017 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((252662865556804065 / 72057594037927936 : ℚ) : ℝ) ≤ ((2133 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2133 / 64 : ℚ) : ℝ) ≤ Real.exp ((63165716389201017 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_291 : heightPower (291 : Fin 988) ≤ ((1321215853425171 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_291
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_291 : heightFactor (291 : Fin 988) ≤ ((160466817583307 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_291
  obtain ⟨hpl, hph⟩ := kernel_bounds_2132
  obtain ⟨hcl, hch⟩ := kernel_bounds_2133
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2133
  have h : (((4549689 / 2048 : ℚ) : ℝ) * (logKernel ((533 / 16 : ℚ) : ℝ) - logKernel ((2133 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2133 / 64 : ℚ) : ℝ) + Real.log ((2133 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((160466817583307 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_292 : ((252696639916005909 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1067 / 32 : ℚ) : ℝ) ∧
    Real.log ((1067 / 32 : ℚ) : ℝ) ≤ ((31587079989500739 / 9007199254740992 : ℚ) : ℝ) := by
  have hl : Real.exp ((252696639916005909 / 72057594037927936 : ℚ) : ℝ) ≤ ((1067 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1067 / 32 : ℚ) : ℝ) ≤ Real.exp ((31587079989500739 / 9007199254740992 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_292 : heightPower (292 : Fin 988) ≤ ((331436457756727 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_292
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_292 : heightFactor (292 : Fin 988) ≤ ((156513015879705 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_292
  obtain ⟨hpl, hph⟩ := kernel_bounds_2133
  obtain ⟨hcl, hch⟩ := kernel_bounds_2134
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2134
  have h : (((1138489 / 512 : ℚ) : ℝ) * (logKernel ((2133 / 64 : ℚ) : ℝ) - logKernel ((1067 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1067 / 32 : ℚ) : ℝ) + Real.log ((1067 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((156513015879705 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_293 : ((252730398452129545 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2135 / 64 : ℚ) : ℝ) ∧
    Real.log ((2135 / 64 : ℚ) : ℝ) ≤ ((63182599613032387 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((252730398452129545 / 72057594037927936 : ℚ) : ℝ) ≤ ((2135 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2135 / 64 : ℚ) : ℝ) ≤ Real.exp ((63182599613032387 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_293 : heightPower (293 : Fin 988) ≤ ((1330275746819745 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_293
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_293 : heightFactor (293 : Fin 988) ≤ ((152656555151931 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_293
  obtain ⟨hpl, hph⟩ := kernel_bounds_2134
  obtain ⟨hcl, hch⟩ := kernel_bounds_2135
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2135
  have h : (((4558225 / 2048 : ℚ) : ℝ) * (logKernel ((1067 / 32 : ℚ) : ℝ) - logKernel ((2135 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2135 / 64 : ℚ) : ℝ) + Real.log ((2135 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((152656555151931 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_294 : ((252764141179994057 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((267 / 8 : ℚ) : ℝ) ∧
    Real.log ((267 / 8 : ℚ) : ℝ) ≤ ((63191035294998515 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((252764141179994057 / 72057594037927936 : ℚ) : ℝ) ≤ ((267 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((267 / 8 : ℚ) : ℝ) ≤ Real.exp ((63191035294998515 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_294 : heightPower (294 : Fin 988) ≤ ((1334805600861569 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_294
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_294 : heightFactor (294 : Fin 988) ≤ ((297790081810879 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_294
  obtain ⟨hpl, hph⟩ := kernel_bounds_2135
  obtain ⟨hcl, hch⟩ := kernel_bounds_2136
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2136
  have h : (((71289 / 32 : ℚ) : ℝ) * (logKernel ((2135 / 64 : ℚ) : ℝ) - logKernel ((267 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((267 / 8 : ℚ) : ℝ) + Real.log ((267 / 8 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((297790081810879 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_295 : ((63199467028599431 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((2137 / 64 : ℚ) : ℝ) ∧
    Real.log ((2137 / 64 : ℚ) : ℝ) ≤ ((252797868114397727 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((63199467028599431 / 18014398509481984 : ℚ) : ℝ) ≤ ((2137 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2137 / 64 : ℚ) : ℝ) ≤ Real.exp ((252797868114397727 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_295 : heightPower (295 : Fin 988) ≤ ((334833848302547 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_295
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_295 : heightFactor (295 : Fin 988) ≤ ((36306534374199 / 35184372088832 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_295
  obtain ⟨hpl, hph⟩ := kernel_bounds_2136
  obtain ⟨hcl, hch⟩ := kernel_bounds_2137
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2137
  have h : (((4566769 / 2048 : ℚ) : ℝ) * (logKernel ((267 / 8 : ℚ) : ℝ) - logKernel ((2137 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2137 / 64 : ℚ) : ℝ) + Real.log ((2137 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((36306534374199 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_296 : ((252831579270118053 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1069 / 32 : ℚ) : ℝ) ∧
    Real.log ((1069 / 32 : ℚ) : ℝ) ≤ ((31603947408764757 / 9007199254740992 : ℚ) : ℝ) := by
  have hl : Real.exp ((252831579270118053 / 72057594037927936 : ℚ) : ℝ) ≤ ((1069 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1069 / 32 : ℚ) : ℝ) ≤ Real.exp ((31603947408764757 / 9007199254740992 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_296 : heightPower (296 : Fin 988) ≤ ((335966280980831 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_296
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_296 : heightFactor (296 : Fin 988) ≤ ((70823783344281 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_296
  obtain ⟨hpl, hph⟩ := kernel_bounds_2137
  obtain ⟨hcl, hch⟩ := kernel_bounds_2138
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2138
  have h : (((1142761 / 512 : ℚ) : ℝ) * (logKernel ((2137 / 64 : ℚ) : ℝ) - logKernel ((1069 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1069 / 32 : ℚ) : ℝ) + Real.log ((1069 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((70823783344281 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_297 : ((252865274661911821 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2139 / 64 : ℚ) : ℝ) ∧
    Real.log ((2139 / 64 : ℚ) : ℝ) ≤ ((15804079666369489 / 4503599627370496 : ℚ) : ℝ) := by
  have hl : Real.exp ((252865274661911821 / 72057594037927936 : ℚ) : ℝ) ≤ ((2139 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2139 / 64 : ℚ) : ℝ) ≤ Real.exp ((15804079666369489 / 4503599627370496 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_297 : heightPower (297 : Fin 988) ≤ ((1348394793058623 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_297
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_297 : heightFactor (297 : Fin 988) ≤ ((69078553119817 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_297
  obtain ⟨hpl, hph⟩ := kernel_bounds_2138
  obtain ⟨hcl, hch⟩ := kernel_bounds_2139
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2139
  have h : (((4575321 / 2048 : ℚ) : ℝ) * (logKernel ((1069 / 32 : ℚ) : ℝ) - logKernel ((2139 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2139 / 64 : ℚ) : ℝ) + Real.log ((2139 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((69078553119817 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_298 : ((252898954304515115 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((535 / 16 : ℚ) : ℝ) ∧
    Real.log ((535 / 16 : ℚ) : ℝ) ≤ ((126449477152257559 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((252898954304515115 / 72057594037927936 : ℚ) : ℝ) ≤ ((535 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((535 / 16 : ℚ) : ℝ) ≤ Real.exp ((126449477152257559 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_298 : heightPower (298 : Fin 988) ≤ ((676462200336823 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_298
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_298 : heightFactor (298 : Fin 988) ≤ ((8422036783135 / 8796093022208 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_298
  obtain ⟨hpl, hph⟩ := kernel_bounds_2139
  obtain ⟨hcl, hch⟩ := kernel_bounds_2140
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2140
  have h : (((286225 / 128 : ℚ) : ℝ) * (logKernel ((2139 / 64 : ℚ) : ℝ) - logKernel ((535 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((535 / 16 : ℚ) : ℝ) + Real.log ((535 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((8422036783135 / 8796093022208 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_299 : ((126466309106321683 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2141 / 64 : ℚ) : ℝ) ∧
    Real.log ((2141 / 64 : ℚ) : ℝ) ≤ ((252932618212643369 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((126466309106321683 / 36028797018963968 : ℚ) : ℝ) ≤ ((2141 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2141 / 64 : ℚ) : ℝ) ≤ Real.exp ((252932618212643369 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_299 : heightPower (299 : Fin 988) ≤ ((339363486706469 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_299
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_299 : heightFactor (299 : Fin 988) ≤ ((262863798440393 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_299
  obtain ⟨hpl, hph⟩ := kernel_bounds_2140
  obtain ⟨hcl, hch⟩ := kernel_bounds_2141
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2141
  have h : (((4583881 / 2048 : ℚ) : ℝ) * (logKernel ((535 / 16 : ℚ) : ℝ) - logKernel ((2141 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2141 / 64 : ℚ) : ℝ) + Real.log ((2141 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((262863798440393 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_300 : ((7905195825030981 / 2251799813685248 : ℚ) : ℝ) ≤ Real.log ((1071 / 32 : ℚ) : ℝ) ∧
    Real.log ((1071 / 32 : ℚ) : ℝ) ≤ ((252966266400991395 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((7905195825030981 / 2251799813685248 : ℚ) : ℝ) ≤ ((1071 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1071 / 32 : ℚ) : ℝ) ≤ Real.exp ((252966266400991395 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_300 : heightPower (300 : Fin 988) ≤ ((680991715786357 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_300
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_300 : heightFactor (300 : Fin 988) ≤ ((256385951882545 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_300
  obtain ⟨hpl, hph⟩ := kernel_bounds_2141
  obtain ⟨hcl, hch⟩ := kernel_bounds_2142
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2142
  have h : (((1147041 / 512 : ℚ) : ℝ) * (logKernel ((2141 / 64 : ℚ) : ℝ) - logKernel ((1071 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1071 / 32 : ℚ) : ℝ) + Real.log ((1071 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((256385951882545 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_301 : ((252999898884233435 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2143 / 64 : ℚ) : ℝ) ∧
    Real.log ((2143 / 64 : ℚ) : ℝ) ≤ ((126499949442116719 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((252999898884233435 / 72057594037927936 : ℚ) : ℝ) ≤ ((2143 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2143 / 64 : ℚ) : ℝ) ≤ Real.exp ((126499949442116719 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_301 : heightPower (301 : Fin 988) ≤ ((683256427485741 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_301
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_301 : heightFactor (301 : Fin 988) ≤ ((250067614040111 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_301
  obtain ⟨hpl, hph⟩ := kernel_bounds_2142
  obtain ⟨hcl, hch⟩ := kernel_bounds_2143
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2143
  have h : (((4592449 / 2048 : ℚ) : ℝ) * (logKernel ((1071 / 32 : ℚ) : ℝ) - logKernel ((2143 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2143 / 64 : ℚ) : ℝ) + Real.log ((2143 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((250067614040111 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_302 : ((253033515677023197 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((67 / 2 : ℚ) : ℝ) ∧
    Real.log ((67 / 2 : ℚ) : ℝ) ≤ ((7907297364906975 / 2251799813685248 : ℚ) : ℝ) := by
  have hl : Real.exp ((253033515677023197 / 72057594037927936 : ℚ) : ℝ) ≤ ((67 / 2 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((67 / 2 : ℚ) : ℝ) ≤ Real.exp ((7907297364906975 / 2251799813685248 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_302 : heightPower (302 : Fin 988) ≤ ((1371042217079421 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_302
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_302 : heightFactor (302 : Fin 988) ≤ ((121952430233331 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_302
  obtain ⟨hpl, hph⟩ := kernel_bounds_2143
  obtain ⟨hcl, hch⟩ := kernel_bounds_2144
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2144
  have h : (((4489 / 2 : ℚ) : ℝ) * (logKernel ((2143 / 64 : ℚ) : ℝ) - logKernel ((67 / 2 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((67 / 2 : ℚ) : ℝ) + Real.log ((67 / 2 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((121952430233331 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_303 : ((253067116793993883 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2145 / 64 : ℚ) : ℝ) ∧
    Real.log ((2145 / 64 : ℚ) : ℝ) ≤ ((126533558396996943 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((253067116793993883 / 72057594037927936 : ℚ) : ℝ) ≤ ((2145 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2145 / 64 : ℚ) : ℝ) ≤ Real.exp ((126533558396996943 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_303 : heightPower (303 : Fin 988) ≤ ((343892879488423 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_303
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_303 : heightFactor (303 : Fin 988) ≤ ((59473465796767 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_303
  obtain ⟨hpl, hph⟩ := kernel_bounds_2144
  obtain ⟨hcl, hch⟩ := kernel_bounds_2145
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2145
  have h : (((4601025 / 2048 : ℚ) : ℝ) * (logKernel ((67 / 2 : ℚ) : ℝ) - logKernel ((2145 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2145 / 64 : ℚ) : ℝ) + Real.log ((2145 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((59473465796767 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_304 : ((253100702249758237 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1073 / 32 : ℚ) : ℝ) ∧
    Real.log ((1073 / 32 : ℚ) : ℝ) ≤ ((7909396945304945 / 2251799813685248 : ℚ) : ℝ) := by
  have hl : Real.exp ((253100702249758237 / 72057594037927936 : ℚ) : ℝ) ≤ ((1073 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1073 / 32 : ℚ) : ℝ) ≤ Real.exp ((7909396945304945 / 2251799813685248 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_304 : heightPower (304 : Fin 988) ≤ ((86256297353211 / 17592186044416 : ℚ) : ℝ) := by
  have hh := log_height_bounds_304
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_304 : heightFactor (304 : Fin 988) ≤ ((232030888328153 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_304
  obtain ⟨hpl, hph⟩ := kernel_bounds_2145
  obtain ⟨hcl, hch⟩ := kernel_bounds_2146
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2146
  have h : (((1151329 / 512 : ℚ) : ℝ) * (logKernel ((2145 / 64 : ℚ) : ℝ) - logKernel ((1073 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1073 / 32 : ℚ) : ℝ) + Real.log ((1073 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((232030888328153 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_305 : ((253134272058908577 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2147 / 64 : ℚ) : ℝ) ∧
    Real.log ((2147 / 64 : ℚ) : ℝ) ≤ ((63283568014727145 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((253134272058908577 / 72057594037927936 : ℚ) : ℝ) ≤ ((2147 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2147 / 64 : ℚ) : ℝ) ≤ Real.exp ((63283568014727145 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_305 : heightPower (305 : Fin 988) ≤ ((1384629936229473 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_305
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_305 : heightFactor (305 : Fin 988) ≤ ((113156146903743 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_305
  obtain ⟨hpl, hph⟩ := kernel_bounds_2146
  obtain ⟨hcl, hch⟩ := kernel_bounds_2147
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2147
  have h : (((4609609 / 2048 : ℚ) : ℝ) * (logKernel ((1073 / 32 : ℚ) : ℝ) - logKernel ((2147 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2147 / 64 : ℚ) : ℝ) + Real.log ((2147 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((113156146903743 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_306 : ((126583913118008419 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((537 / 16 : ℚ) : ℝ) ∧
    Real.log ((537 / 16 : ℚ) : ℝ) ≤ ((253167826236016841 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((126583913118008419 / 36028797018963968 : ℚ) : ℝ) ≤ ((537 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((537 / 16 : ℚ) : ℝ) ≤ Real.exp ((253167826236016841 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_306 : heightPower (306 : Fin 988) ≤ ((694579526872453 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_306
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_306 : heightFactor (306 : Fin 988) ≤ ((220734527078885 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_306
  obtain ⟨hpl, hph⟩ := kernel_bounds_2147
  obtain ⟨hcl, hch⟩ := kernel_bounds_2148
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2148
  have h : (((288369 / 128 : ℚ) : ℝ) * (logKernel ((2147 / 64 : ℚ) : ℝ) - logKernel ((537 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((537 / 16 : ℚ) : ℝ) + Real.log ((537 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((220734527078885 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_307 : ((253201364795634609 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2149 / 64 : ℚ) : ℝ) ∧
    Real.log ((2149 / 64 : ℚ) : ℝ) ≤ ((63300341198908653 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((253201364795634609 / 72057594037927936 : ℚ) : ℝ) ≤ ((2149 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2149 / 64 : ℚ) : ℝ) ≤ Real.exp ((63300341198908653 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_307 : heightPower (307 : Fin 988) ≤ ((1393688110254517 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_307
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_307 : heightFactor (307 : Fin 988) ≤ ((107647061466623 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_307
  obtain ⟨hpl, hph⟩ := kernel_bounds_2148
  obtain ⟨hcl, hch⟩ := kernel_bounds_2149
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2149
  have h : (((4618201 / 2048 : ℚ) : ℝ) * (logKernel ((537 / 16 : ℚ) : ℝ) - logKernel ((2149 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2149 / 64 : ℚ) : ℝ) + Real.log ((2149 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((107647061466623 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_308 : ((126617443876146583 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((1075 / 32 : ℚ) : ℝ) ∧
    Real.log ((1075 / 32 : ℚ) : ℝ) ≤ ((253234887752293169 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((126617443876146583 / 36028797018963968 : ℚ) : ℝ) ≤ ((1075 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1075 / 32 : ℚ) : ℝ) ≤ Real.exp ((253234887752293169 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_308 : heightPower (308 : Fin 988) ≤ ((1398217105815069 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_308
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_308 : heightFactor (308 : Fin 988) ≤ ((209987701353333 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_308
  obtain ⟨hpl, hph⟩ := kernel_bounds_2149
  obtain ⟨hcl, hch⟩ := kernel_bounds_2150
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2150
  have h : (((1155625 / 512 : ℚ) : ℝ) * (logKernel ((2149 / 64 : ℚ) : ℝ) - logKernel ((1075 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1075 / 32 : ℚ) : ℝ) + Real.log ((1075 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((209987701353333 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_309 : ((126634197560251759 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2151 / 64 : ℚ) : ℝ) ∧
    Real.log ((2151 / 64 : ℚ) : ℝ) ≤ ((253268395120503521 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((126634197560251759 / 36028797018963968 : ℚ) : ℝ) ≤ ((2151 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2151 / 64 : ℚ) : ℝ) ≤ Real.exp ((253268395120503521 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_309 : heightPower (309 : Fin 988) ≤ ((350686510120811 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_309
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_309 : heightFactor (309 : Fin 988) ≤ ((51202991355303 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_309
  obtain ⟨hpl, hph⟩ := kernel_bounds_2150
  obtain ⟨hcl, hch⟩ := kernel_bounds_2151
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2151
  have h : (((4626801 / 2048 : ℚ) : ℝ) * (logKernel ((1075 / 32 : ℚ) : ℝ) - logKernel ((2151 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2151 / 64 : ℚ) : ℝ) + Real.log ((2151 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((51202991355303 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_310 : ((253301886914756437 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((269 / 8 : ℚ) : ℝ) ∧
    Real.log ((269 / 8 : ℚ) : ℝ) ≤ ((31662735864344555 / 9007199254740992 : ℚ) : ℝ) := by
  have hl : Real.exp ((253301886914756437 / 72057594037927936 : ℚ) : ℝ) ≤ ((269 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((269 / 8 : ℚ) : ℝ) ≤ Real.exp ((31662735864344555 / 9007199254740992 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_310 : heightPower (310 : Fin 988) ≤ ((1407274914315649 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_310
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_310 : heightFactor (310 : Fin 988) ≤ ((99881849638519 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_310
  obtain ⟨hpl, hph⟩ := kernel_bounds_2151
  obtain ⟨hcl, hch⟩ := kernel_bounds_2152
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2152
  have h : (((72361 / 32 : ℚ) : ℝ) * (logKernel ((2151 / 64 : ℚ) : ℝ) - logKernel ((269 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((269 / 8 : ℚ) : ℝ) + Real.log ((269 / 8 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((99881849638519 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_311 : ((253335363149522499 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2153 / 64 : ℚ) : ℝ) ∧
    Real.log ((2153 / 64 : ℚ) : ℝ) ≤ ((126667681574761251 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((253335363149522499 / 72057594037927936 : ℚ) : ℝ) ≤ ((2153 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2153 / 64 : ℚ) : ℝ) ≤ Real.exp ((126667681574761251 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_311 : heightPower (311 : Fin 988) ≤ ((176475465921101 / 35184372088832 : ℚ) : ℝ) := by
  have hh := log_height_bounds_311
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_311 : heightFactor (311 : Fin 988) ≤ ((194839766127933 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_311
  obtain ⟨hpl, hph⟩ := kernel_bounds_2152
  obtain ⟨hcl, hch⟩ := kernel_bounds_2153
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2153
  have h : (((4635409 / 2048 : ℚ) : ℝ) * (logKernel ((269 / 8 : ℚ) : ℝ) - logKernel ((2153 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2153 / 64 : ℚ) : ℝ) + Real.log ((2153 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((194839766127933 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_312 : ((253368823839252123 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1077 / 32 : ℚ) : ℝ) ∧
    Real.log ((1077 / 32 : ℚ) : ℝ) ≤ ((126684411919626063 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((253368823839252123 / 72057594037927936 : ℚ) : ℝ) ≤ ((1077 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1077 / 32 : ℚ) : ℝ) ≤ Real.exp ((126684411919626063 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_312 : heightPower (312 : Fin 988) ≤ ((44260389990599 / 8796093022208 : ℚ) : ℝ) := by
  have hh := log_height_bounds_312
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_312 : heightFactor (312 : Fin 988) ≤ ((190037106305727 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_312
  obtain ⟨hpl, hph⟩ := kernel_bounds_2153
  obtain ⟨hcl, hch⟩ := kernel_bounds_2154
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2154
  have h : (((1159929 / 512 : ℚ) : ℝ) * (logKernel ((2153 / 64 : ℚ) : ℝ) - logKernel ((1077 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1077 / 32 : ℚ) : ℝ) + Real.log ((1077 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((190037106305727 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_313 : ((253402268998375607 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2155 / 64 : ℚ) : ℝ) ∧
    Real.log ((2155 / 64 : ℚ) : ℝ) ≤ ((126701134499187805 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((253402268998375607 / 72057594037927936 : ℚ) : ℝ) ≤ ((2155 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2155 / 64 : ℚ) : ℝ) ≤ Real.exp ((126701134499187805 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_313 : heightPower (313 : Fin 988) ≤ ((710430585681549 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_313
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_313 : heightFactor (313 : Fin 988) ≤ ((185352735372373 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_313
  obtain ⟨hpl, hph⟩ := kernel_bounds_2154
  obtain ⟨hcl, hch⟩ := kernel_bounds_2155
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2155
  have h : (((4644025 / 2048 : ℚ) : ℝ) * (logKernel ((1077 / 32 : ℚ) : ℝ) - logKernel ((2155 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2155 / 64 : ℚ) : ℝ) + Real.log ((2155 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((185352735372373 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_314 : ((253435698641303161 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((539 / 16 : ℚ) : ℝ) ∧
    Real.log ((539 / 16 : ℚ) : ℝ) ≤ ((63358924660325791 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((253435698641303161 / 72057594037927936 : ℚ) : ℝ) ≤ ((539 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((539 / 16 : ℚ) : ℝ) ≤ Real.exp ((63358924660325791 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_314 : heightPower (314 : Fin 988) ≤ ((178173725302111 / 35184372088832 : ℚ) : ℝ) := by
  have hh := log_height_bounds_314
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_314 : heightFactor (314 : Fin 988) ≤ ((90391871135927 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_314
  obtain ⟨hpl, hph⟩ := kernel_bounds_2155
  obtain ⟨hcl, hch⟩ := kernel_bounds_2156
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2156
  have h : (((290521 / 128 : ℚ) : ℝ) * (logKernel ((2155 / 64 : ℚ) : ℝ) - logKernel ((539 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((539 / 16 : ℚ) : ℝ) + Real.log ((539 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((90391871135927 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_315 : ((126734556391212477 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2157 / 64 : ℚ) : ℝ) ∧
    Real.log ((2157 / 64 : ℚ) : ℝ) ≤ ((253469112782424957 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((126734556391212477 / 36028797018963968 : ℚ) : ℝ) ≤ ((2157 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2157 / 64 : ℚ) : ℝ) ≤ Real.exp ((253469112782424957 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_315 : heightPower (315 : Fin 988) ≤ ((1429918372916749 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_315
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_315 : heightFactor (315 : Fin 988) ≤ ((176327287527445 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_315
  obtain ⟨hpl, hph⟩ := kernel_bounds_2156
  obtain ⟨hcl, hch⟩ := kernel_bounds_2157
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2157
  have h : (((4652649 / 2048 : ℚ) : ℝ) * (logKernel ((539 / 16 : ℚ) : ℝ) - logKernel ((2157 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2157 / 64 : ℚ) : ℝ) + Real.log ((2157 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((176327287527445 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_316 : ((253502511436111141 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1079 / 32 : ℚ) : ℝ) ∧
    Real.log ((1079 / 32 : ℚ) : ℝ) ≤ ((31687813929513893 / 9007199254740992 : ℚ) : ℝ) := by
  have hl : Real.exp ((253502511436111141 / 72057594037927936 : ℚ) : ℝ) ≤ ((1079 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1079 / 32 : ℚ) : ℝ) ≤ Real.exp ((31687813929513893 / 9007199254740992 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_316 : heightPower (316 : Fin 988) ≤ ((1434446882918815 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_316
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_316 : heightFactor (316 : Fin 988) ≤ ((171980601483233 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_316
  obtain ⟨hpl, hph⟩ := kernel_bounds_2157
  obtain ⟨hcl, hch⟩ := kernel_bounds_2158
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2158
  have h : (((1164241 / 512 : ℚ) : ℝ) * (logKernel ((2157 / 64 : ℚ) : ℝ) - logKernel ((1079 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1079 / 32 : ℚ) : ℝ) + Real.log ((1079 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((171980601483233 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_317 : ((63383973654177977 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((2159 / 64 : ℚ) : ℝ) ∧
    Real.log ((2159 / 64 : ℚ) : ℝ) ≤ ((253535894616711911 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((63383973654177977 / 18014398509481984 : ℚ) : ℝ) ≤ ((2159 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2159 / 64 : ℚ) : ℝ) ≤ Real.exp ((253535894616711911 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_317 : heightPower (317 : Fin 988) ≤ ((359743833119785 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_317
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_317 : heightFactor (317 : Fin 988) ≤ ((167740982588781 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_317
  obtain ⟨hpl, hph⟩ := kernel_bounds_2158
  obtain ⟨hcl, hch⟩ := kernel_bounds_2159
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2159
  have h : (((4661281 / 2048 : ℚ) : ℝ) * (logKernel ((1079 / 32 : ℚ) : ℝ) - logKernel ((2159 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2159 / 64 : ℚ) : ℝ) + Real.log ((2159 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((167740982588781 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_318 : ((126784631169278751 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((135 / 4 : ℚ) : ℝ) ∧
    Real.log ((135 / 4 : ℚ) : ℝ) ≤ ((253569262338557505 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((126784631169278751 / 36028797018963968 : ℚ) : ℝ) ≤ ((135 / 4 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((135 / 4 : ℚ) : ℝ) ≤ Real.exp ((253569262338557505 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_318 : heightPower (318 : Fin 988) ≤ ((180437965206713 / 35184372088832 : ℚ) : ℝ) := by
  have hh := log_height_bounds_318
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_318 : heightFactor (318 : Fin 988) ≤ ((20450724465739 / 35184372088832 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_318
  obtain ⟨hpl, hph⟩ := kernel_bounds_2159
  obtain ⟨hcl, hch⟩ := kernel_bounds_2160
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2160
  have h : (((18225 / 8 : ℚ) : ℝ) * (logKernel ((2159 / 64 : ℚ) : ℝ) - logKernel ((135 / 4 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((135 / 4 : ℚ) : ℝ) + Real.log ((135 / 4 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((20450724465739 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_319 : ((253602614615958275 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2161 / 64 : ℚ) : ℝ) ∧
    Real.log ((2161 / 64 : ℚ) : ℝ) ≤ ((126801307307979139 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((253602614615958275 / 72057594037927936 : ℚ) : ℝ) ≤ ((2161 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2161 / 64 : ℚ) : ℝ) ≤ Real.exp ((126801307307979139 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_319 : heightPower (319 : Fin 988) ≤ ((1448032050498405 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_319
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_319 : heightFactor (319 : Fin 988) ≤ ((39893117644137 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_319
  obtain ⟨hpl, hph⟩ := kernel_bounds_2160
  obtain ⟨hcl, hch⟩ := kernel_bounds_2161
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2161
  have h : (((4669921 / 2048 : ℚ) : ℝ) * (logKernel ((135 / 4 : ℚ) : ℝ) - logKernel ((2161 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2161 / 64 : ℚ) : ℝ) + Real.log ((2161 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((39893117644137 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

end LegendreK6.M2Pilot.Enclosures.Height009
