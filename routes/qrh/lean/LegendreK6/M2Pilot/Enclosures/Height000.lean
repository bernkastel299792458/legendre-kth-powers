import LegendreK6.M2PilotDefinitions
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp

/-! Generated proposals: every bound is checked by Lean, not by trusting Arb. -/
namespace LegendreK6.M2Pilot.Enclosures.Height000
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem height_z_bounds_1841 : ((8942692747815307611 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1841 / 64 : ℚ) : ℝ) ∧
    heightZ ((1841 / 64 : ℚ) : ℝ) ≤ ((4471346373907653807 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((8942692747815307611 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1841 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((205 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((1841 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((205 / 192 : ℚ) : ℝ) ≤ ((4471346373907653807 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1841 : ((36028797018963967 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((1841 / 64 : ℚ) : ℝ) ∧
    logKernel ((1841 / 64 : ℚ) : ℝ) ≤ ((36028797018963969 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1841
  constructor
  · exact (show ((36028797018963967 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((8942692747815307611 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1841 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((4471346373907653807 / 9223372036854775808 : ℚ) : ℝ) ≤ ((36028797018963969 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1842 : ((4402024573729137795 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((921 / 32 : ℚ) : ℝ) ∧
    heightZ ((921 / 32 : ℚ) : ℝ) ≤ ((8804049147458275593 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((4402024573729137795 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((921 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((101 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((921 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((101 / 96 : ℚ) : ℝ) ≤ ((8804049147458275593 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1842 : ((35500198175234981 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((921 / 32 : ℚ) : ℝ) ∧
    logKernel ((921 / 32 : ℚ) : ℝ) ≤ ((71000396350469967 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1842
  constructor
  · exact (show ((35500198175234981 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((4402024573729137795 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((921 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((8804049147458275593 / 18446744073709551616 : ℚ) : ℝ) ≤ ((71000396350469967 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1843 : ((8667555016893175797 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1843 / 64 : ℚ) : ℝ) ∧
    heightZ ((1843 / 64 : ℚ) : ℝ) ≤ ((1083444377111646975 / 2305843009213693952 : ℚ) : ℝ) := by
  have h : ((8667555016893175797 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1843 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((199 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((1843 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((199 / 192 : ℚ) : ℝ) ≤ ((1083444377111646975 / 2305843009213693952 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1843 : ((8737454654126185 / 9007199254740992 : ℚ) : ℝ) ≤ logKernel ((1843 / 64 : ℚ) : ℝ) ∧
    logKernel ((1843 / 64 : ℚ) : ℝ) ≤ ((69899637233009485 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1843
  constructor
  · exact (show ((8737454654126185 / 9007199254740992 : ℚ) : ℝ) ≤ zKernel ((8667555016893175797 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1843 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1083444377111646975 / 2305843009213693952 : ℚ) : ℝ) ≤ ((69899637233009485 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1844 : ((4266588515839842019 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((461 / 16 : ℚ) : ℝ) ∧
    heightZ ((461 / 16 : ℚ) : ℝ) ≤ ((8533177031679684041 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((4266588515839842019 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((461 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((49 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((461 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((49 / 48 : ℚ) : ℝ) ≤ ((8533177031679684041 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1844 : ((68815943803868417 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((461 / 16 : ℚ) : ℝ) ∧
    logKernel ((461 / 16 : ℚ) : ℝ) ≤ ((34407971901934211 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1844
  constructor
  · exact (show ((68815943803868417 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((4266588515839842019 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((461 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((8533177031679684041 / 18446744073709551616 : ℚ) : ℝ) ≤ ((34407971901934211 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1845 : ((4200441192012517973 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((1845 / 64 : ℚ) : ℝ) ∧
    heightZ ((1845 / 64 : ℚ) : ℝ) ≤ ((8400882384025035949 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((4200441192012517973 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((1845 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((193 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((1845 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((193 / 192 : ℚ) : ℝ) ≤ ((8400882384025035949 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1845 : ((16937262871018217 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((1845 / 64 : ℚ) : ℝ) ∧
    logKernel ((1845 / 64 : ℚ) : ℝ) ≤ ((67749051484072873 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1845
  constructor
  · exact (show ((16937262871018217 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((4200441192012517973 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1845 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((8400882384025035949 / 18446744073709551616 : ℚ) : ℝ) ≤ ((67749051484072873 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1846 : ((8270638774774148991 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((923 / 32 : ℚ) : ℝ) ∧
    heightZ ((923 / 32 : ℚ) : ℝ) ≤ ((4135319387387074497 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((8270638774774148991 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((923 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((95 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((923 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((95 / 96 : ℚ) : ℝ) ≤ ((4135319387387074497 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1846 : ((66698699796565715 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((923 / 32 : ℚ) : ℝ) ∧
    logKernel ((923 / 32 : ℚ) : ℝ) ≤ ((8337337474570715 / 9007199254740992 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1846
  constructor
  · exact (show ((66698699796565715 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((8270638774774148991 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((923 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((4135319387387074497 / 9223372036854775808 : ℚ) : ℝ) ≤ ((8337337474570715 / 9007199254740992 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1847 : ((8142414405523926133 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1847 / 64 : ℚ) : ℝ) ∧
    heightZ ((1847 / 64 : ℚ) : ℝ) ≤ ((1017801800690490767 / 2305843009213693952 : ℚ) : ℝ) := by
  have h : ((8142414405523926133 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1847 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((187 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((1847 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((187 / 192 : ℚ) : ℝ) ≤ ((1017801800690490767 / 2305843009213693952 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1847 : ((65664632302612305 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1847 / 64 : ℚ) : ℝ) ∧
    logKernel ((1847 / 64 : ℚ) : ℝ) ≤ ((32832316151306155 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1847
  constructor
  · exact (show ((65664632302612305 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((8142414405523926133 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1847 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1017801800690490767 / 2305843009213693952 : ℚ) : ℝ) ≤ ((32832316151306155 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1848 : ((8016177970859815879 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((231 / 8 : ℚ) : ℝ) ∧
    heightZ ((231 / 8 : ℚ) : ℝ) ≤ ((4008088985429907941 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((8016177970859815879 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((231 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((23 / 24 : ℚ) : ℝ) ∧
      Real.exp (-((231 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((23 / 24 : ℚ) : ℝ) ≤ ((4008088985429907941 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1848 : ((64646596539192061 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((231 / 8 : ℚ) : ℝ) ∧
    logKernel ((231 / 8 : ℚ) : ℝ) ≤ ((32323298269596033 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1848
  constructor
  · exact (show ((64646596539192061 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((8016177970859815879 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((231 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((4008088985429907941 / 9223372036854775808 : ℚ) : ℝ) ≤ ((32323298269596033 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1849 : ((986487331339091663 / 2305843009213693952 : ℚ) : ℝ) ≤ heightZ ((1849 / 64 : ℚ) : ℝ) ∧
    heightZ ((1849 / 64 : ℚ) : ℝ) ≤ ((7891898650712733307 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((986487331339091663 / 2305843009213693952 : ℚ) : ℝ) ≤ Real.exp (-((1849 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((181 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((1849 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((181 / 192 : ℚ) : ℝ) ≤ ((7891898650712733307 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1849 : ((31822171978680375 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((1849 / 64 : ℚ) : ℝ) ∧
    logKernel ((1849 / 64 : ℚ) : ℝ) ≤ ((63644343957360755 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1849
  constructor
  · exact (show ((31822171978680375 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((986487331339091663 / 2305843009213693952 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1849 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((7891898650712733307 / 18446744073709551616 : ℚ) : ℝ) ≤ ((63644343957360755 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1850 : ((7769546102834476041 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((925 / 32 : ℚ) : ℝ) ∧
    heightZ ((925 / 32 : ℚ) : ℝ) ≤ ((1942386525708619011 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((7769546102834476041 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((925 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((89 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((925 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((89 / 96 : ℚ) : ℝ) ≤ ((1942386525708619011 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1850 : ((62657629861568353 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((925 / 32 : ℚ) : ℝ) ∧
    logKernel ((925 / 32 : ℚ) : ℝ) ≤ ((31328814930784179 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1850
  constructor
  · exact (show ((62657629861568353 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((7769546102834476041 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((925 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1942386525708619011 / 4611686018427387904 : ℚ) : ℝ) ≤ ((31328814930784179 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1851 : ((3824545227694899061 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((1851 / 64 : ℚ) : ℝ) ∧
    heightZ ((1851 / 64 : ℚ) : ℝ) ≤ ((7649090455389798125 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((3824545227694899061 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((1851 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((175 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((1851 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((175 / 192 : ℚ) : ℝ) ≤ ((7649090455389798125 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1851 : ((15421553337479431 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((1851 / 64 : ℚ) : ℝ) ∧
    logKernel ((1851 / 64 : ℚ) : ℝ) ≤ ((61686213349917729 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1851
  constructor
  · exact (show ((15421553337479431 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((3824545227694899061 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1851 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((7649090455389798125 / 18446744073709551616 : ℚ) : ℝ) ≤ ((61686213349917729 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1852 : ((1882625574915833271 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((463 / 16 : ℚ) : ℝ) ∧
    heightZ ((463 / 16 : ℚ) : ℝ) ≤ ((7530502299663333087 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((1882625574915833271 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((463 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((43 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((463 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((43 / 48 : ℚ) : ℝ) ≤ ((7530502299663333087 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1852 : ((30364928627674729 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((463 / 16 : ℚ) : ℝ) ∧
    logKernel ((463 / 16 : ℚ) : ℝ) ≤ ((60729857255349463 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1852
  constructor
  · exact (show ((30364928627674729 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((1882625574915833271 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((463 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((7530502299663333087 / 18446744073709551616 : ℚ) : ℝ) ≤ ((60729857255349463 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1853 : ((7413752682879585735 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1853 / 64 : ℚ) : ℝ) ∧
    heightZ ((1853 / 64 : ℚ) : ℝ) ≤ ((3706876341439792869 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((7413752682879585735 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1853 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((169 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((1853 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((169 / 192 : ℚ) : ℝ) ≤ ((3706876341439792869 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1853 : ((1868385252741831 / 2251799813685248 : ℚ) : ℝ) ≤ logKernel ((1853 / 64 : ℚ) : ℝ) ∧
    logKernel ((1853 / 64 : ℚ) : ℝ) ≤ ((59788328087738597 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1853
  constructor
  · exact (show ((1868385252741831 / 2251799813685248 : ℚ) : ℝ) ≤ zKernel ((7413752682879585735 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1853 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((3706876341439792869 / 9223372036854775808 : ℚ) : ℝ) ≤ ((59788328087738597 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1854 : ((912351637641779955 / 2305843009213693952 : ℚ) : ℝ) ≤ heightZ ((927 / 32 : ℚ) : ℝ) ∧
    heightZ ((927 / 32 : ℚ) : ℝ) ≤ ((7298813101134239643 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((912351637641779955 / 2305843009213693952 : ℚ) : ℝ) ≤ Real.exp (-((927 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((83 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((927 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((83 / 96 : ℚ) : ℝ) ≤ ((7298813101134239643 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1854 : ((58861395976889027 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((927 / 32 : ℚ) : ℝ) ∧
    logKernel ((927 / 32 : ℚ) : ℝ) ≤ ((7357674497111129 / 9007199254740992 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1854
  constructor
  · exact (show ((58861395976889027 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((912351637641779955 / 2305843009213693952 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((927 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((7298813101134239643 / 18446744073709551616 : ℚ) : ℝ) ≤ ((7357674497111129 / 9007199254740992 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1855 : ((7185655492435054529 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1855 / 64 : ℚ) : ℝ) ∧
    heightZ ((1855 / 64 : ℚ) : ℝ) ≤ ((1796413873108763633 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((7185655492435054529 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1855 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((163 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((1855 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((163 / 192 : ℚ) : ℝ) ≤ ((1796413873108763633 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1855 : ((3621802163525733 / 4503599627370496 : ℚ) : ℝ) ≤ logKernel ((1855 / 64 : ℚ) : ℝ) ∧
    logKernel ((1855 / 64 : ℚ) : ℝ) ≤ ((57948834616411733 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1855
  constructor
  · exact (show ((3621802163525733 / 4503599627370496 : ℚ) : ℝ) ≤ zKernel ((7185655492435054529 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1855 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1796413873108763633 / 4611686018427387904 : ℚ) : ℝ) ≤ ((57948834616411733 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1856 : ((1768563057462663645 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((29 / 1 : ℚ) : ℝ) ∧
    heightZ ((29 / 1 : ℚ) : ℝ) ≤ ((7074252229850654583 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((1768563057462663645 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((29 / 1 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((5 / 6 : ℚ) : ℝ) ∧
      Real.exp (-((29 / 1 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((5 / 6 : ℚ) : ℝ) ≤ ((7074252229850654583 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1856 : ((28525210604236509 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((29 / 1 : ℚ) : ℝ) ∧
    logKernel ((29 / 1 : ℚ) : ℝ) ≤ ((57050421208473023 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1856
  constructor
  · exact (show ((28525210604236509 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((1768563057462663645 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((29 / 1 : ℚ) : ℝ)) hh).trans
      (show zKernel ((7074252229850654583 / 18446744073709551616 : ℚ) : ℝ) ≤ ((57050421208473023 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1857 : ((870572014345691863 / 2305843009213693952 : ℚ) : ℝ) ≤ heightZ ((1857 / 64 : ℚ) : ℝ) ∧
    heightZ ((1857 / 64 : ℚ) : ℝ) ≤ ((6964576114765534907 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((870572014345691863 / 2305843009213693952 : ℚ) : ℝ) ≤ Real.exp (-((1857 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((157 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((1857 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((157 / 192 : ℚ) : ℝ) ≤ ((6964576114765534907 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1857 : ((56165936409399473 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1857 / 64 : ℚ) : ℝ) ∧
    logKernel ((1857 / 64 : ℚ) : ℝ) ≤ ((28082968204699739 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1857
  constructor
  · exact (show ((56165936409399473 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((870572014345691863 / 2305843009213693952 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1857 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((6964576114765534907 / 18446744073709551616 : ℚ) : ℝ) ≤ ((28082968204699739 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1858 : ((6856600370239639459 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((929 / 32 : ℚ) : ℝ) ∧
    heightZ ((929 / 32 : ℚ) : ℝ) ≤ ((3428300185119819731 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((6856600370239639459 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((929 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((77 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((929 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((77 / 96 : ℚ) : ℝ) ≤ ((3428300185119819731 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1858 : ((27647582138063061 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((929 / 32 : ℚ) : ℝ) ∧
    logKernel ((929 / 32 : ℚ) : ℝ) ≤ ((55295164276126127 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1858
  constructor
  · exact (show ((27647582138063061 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((6856600370239639459 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((929 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((3428300185119819731 / 9223372036854775808 : ℚ) : ℝ) ≤ ((55295164276126127 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1859 : ((3375149317235444581 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((1859 / 64 : ℚ) : ℝ) ∧
    heightZ ((1859 / 64 : ℚ) : ℝ) ≤ ((6750298634470889165 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((3375149317235444581 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((1859 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((151 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((1859 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((151 / 192 : ℚ) : ℝ) ≤ ((6750298634470889165 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1859 : ((27218946106737455 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((1859 / 64 : ℚ) : ℝ) ∧
    logKernel ((1859 / 64 : ℚ) : ℝ) ≤ ((54437892213474915 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1859
  constructor
  · exact (show ((27218946106737455 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((3375149317235444581 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1859 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((6750298634470889165 / 18446744073709551616 : ℚ) : ℝ) ≤ ((54437892213474915 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1860 : ((6645644954359064115 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((465 / 16 : ℚ) : ℝ) ∧
    heightZ ((465 / 16 : ℚ) : ℝ) ≤ ((3322822477179532059 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((6645644954359064115 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((465 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((37 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((465 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((37 / 48 : ℚ) : ℝ) ≤ ((3322822477179532059 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1860 : ((53593910922250515 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((465 / 16 : ℚ) : ℝ) ∧
    logKernel ((465 / 16 : ℚ) : ℝ) ≤ ((6699238865281315 / 9007199254740992 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1860
  constructor
  · exact (show ((53593910922250515 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((6645644954359064115 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((465 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((3322822477179532059 / 9223372036854775808 : ℚ) : ℝ) ≤ ((6699238865281315 / 9007199254740992 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1861 : ((3271306889584734293 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((1861 / 64 : ℚ) : ℝ) ∧
    heightZ ((1861 / 64 : ℚ) : ℝ) ≤ ((6542613779169468589 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((3271306889584734293 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((1861 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((145 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((1861 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((145 / 192 : ℚ) : ℝ) ≤ ((6542613779169468589 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1861 : ((52763014348140873 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1861 / 64 : ℚ) : ℝ) ∧
    logKernel ((1861 / 64 : ℚ) : ℝ) ≤ ((26381507174070439 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1861
  constructor
  · exact (show ((52763014348140873 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((3271306889584734293 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1861 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((6542613779169468589 / 18446744073709551616 : ℚ) : ℝ) ≤ ((26381507174070439 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1862 : ((3220589977147415877 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((931 / 32 : ℚ) : ℝ) ∧
    heightZ ((931 / 32 : ℚ) : ℝ) ≤ ((6441179954294831757 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((3220589977147415877 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((931 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((71 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((931 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((71 / 96 : ℚ) : ℝ) ≤ ((6441179954294831757 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1862 : ((51944999631409931 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((931 / 32 : ℚ) : ℝ) ∧
    logKernel ((931 / 32 : ℚ) : ℝ) ≤ ((3246562476963121 / 4503599627370496 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1862
  constructor
  · exact (show ((51944999631409931 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((3220589977147415877 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((931 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((6441179954294831757 / 18446744073709551616 : ℚ) : ℝ) ≤ ((3246562476963121 / 4503599627370496 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1863 : ((6341318715113921225 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1863 / 64 : ℚ) : ℝ) ∧
    heightZ ((1863 / 64 : ℚ) : ℝ) ≤ ((1585329678778480307 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((6341318715113921225 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1863 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((139 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((1863 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((139 / 192 : ℚ) : ℝ) ≤ ((1585329678778480307 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1863 : ((25569833528685165 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((1863 / 64 : ℚ) : ℝ) ∧
    logKernel ((1863 / 64 : ℚ) : ℝ) ≤ ((51139667057370335 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1863
  constructor
  · exact (show ((25569833528685165 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((6341318715113921225 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1863 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1585329678778480307 / 4611686018427387904 : ℚ) : ℝ) ≤ ((51139667057370335 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1864 : ((6243005680945369921 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((233 / 8 : ℚ) : ℝ) ∧
    heightZ ((233 / 8 : ℚ) : ℝ) ≤ ((1560751420236342481 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((6243005680945369921 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((233 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((17 / 24 : ℚ) : ℝ) ∧
      Real.exp (-((233 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((17 / 24 : ℚ) : ℝ) ≤ ((1560751420236342481 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1864 : ((12586705001905987 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((233 / 8 : ℚ) : ℝ) ∧
    logKernel ((233 / 8 : ℚ) : ℝ) ≤ ((50346820007623953 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1864
  constructor
  · exact (show ((12586705001905987 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((6243005680945369921 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((233 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1560751420236342481 / 4611686018427387904 : ℚ) : ℝ) ≤ ((50346820007623953 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1865 : ((6146216849095240189 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1865 / 64 : ℚ) : ℝ) ∧
    heightZ ((1865 / 64 : ℚ) : ℝ) ≤ ((12004329783389141 / 36028797018963968 : ℚ) : ℝ) := by
  have h : ((6146216849095240189 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1865 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((133 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((1865 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((133 / 192 : ℚ) : ℝ) ≤ ((12004329783389141 / 36028797018963968 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1865 : ((24783132456029193 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((1865 / 64 : ℚ) : ℝ) ∧
    logKernel ((1865 / 64 : ℚ) : ℝ) ≤ ((49566264912058391 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1865
  constructor
  · exact (show ((24783132456029193 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((6146216849095240189 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1865 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((12004329783389141 / 36028797018963968 : ℚ) : ℝ) ≤ ((49566264912058391 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1866 : ((6050928588996871875 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((933 / 32 : ℚ) : ℝ) ∧
    heightZ ((933 / 32 : ℚ) : ℝ) ≤ ((3025464294498435939 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((6050928588996871875 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((933 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((65 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((933 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((65 / 96 : ℚ) : ℝ) ≤ ((3025464294498435939 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1866 : ((24398905600793837 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((933 / 32 : ℚ) : ℝ) ∧
    logKernel ((933 / 32 : ℚ) : ℝ) ≤ ((48797811201587679 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1866
  constructor
  · exact (show ((24398905600793837 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((6050928588996871875 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((933 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((3025464294498435939 / 9223372036854775808 : ℚ) : ℝ) ≤ ((48797811201587679 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1867 : ((1489279409110395911 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((1867 / 64 : ℚ) : ℝ) ∧
    heightZ ((1867 / 64 : ℚ) : ℝ) ≤ ((5957117636441583647 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((1489279409110395911 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((1867 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((127 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((1867 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((127 / 192 : ℚ) : ℝ) ≤ ((5957117636441583647 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1867 : ((6005158907703209 / 9007199254740992 : ℚ) : ℝ) ≤ logKernel ((1867 / 64 : ℚ) : ℝ) ∧
    logKernel ((1867 / 64 : ℚ) : ℝ) ≤ ((48041271261625677 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1867
  constructor
  · exact (show ((6005158907703209 / 9007199254740992 : ℚ) : ℝ) ≤ zKernel ((1489279409110395911 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1867 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((5957117636441583647 / 18446744073709551616 : ℚ) : ℝ) ≤ ((48041271261625677 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1868 : ((5864761087898818967 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((467 / 16 : ℚ) : ℝ) ∧
    heightZ ((467 / 16 : ℚ) : ℝ) ≤ ((2932380543949409485 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((5864761087898818967 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((467 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((31 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((467 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((31 / 48 : ℚ) : ℝ) ≤ ((2932380543949409485 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1868 : ((11824115096570199 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((467 / 16 : ℚ) : ℝ) ∧
    logKernel ((467 / 16 : ℚ) : ℝ) ≤ ((47296460386280801 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1868
  constructor
  · exact (show ((11824115096570199 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((5864761087898818967 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((467 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((2932380543949409485 / 9223372036854775808 : ℚ) : ℝ) ≤ ((47296460386280801 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1869 : ((2886918197462175049 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((1869 / 64 : ℚ) : ℝ) ∧
    heightZ ((1869 / 64 : ℚ) : ℝ) ≤ ((5773836394924350101 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((2886918197462175049 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((1869 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((121 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((1869 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((121 / 192 : ℚ) : ℝ) ≤ ((5773836394924350101 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1869 : ((46563196733260885 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1869 / 64 : ℚ) : ℝ) ∧
    logKernel ((1869 / 64 : ℚ) : ℝ) ≤ ((23281598366630445 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1869
  constructor
  · exact (show ((46563196733260885 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((2886918197462175049 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1869 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((5773836394924350101 / 18446744073709551616 : ℚ) : ℝ) ≤ ((23281598366630445 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1870 : ((5684321358655174807 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((935 / 32 : ℚ) : ℝ) ∧
    heightZ ((935 / 32 : ℚ) : ℝ) ≤ ((2842160679327587405 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((5684321358655174807 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((935 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((59 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((935 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((59 / 96 : ℚ) : ℝ) ≤ ((2842160679327587405 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1870 : ((22920650639738607 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((935 / 32 : ℚ) : ℝ) ∧
    logKernel ((935 / 32 : ℚ) : ℝ) ≤ ((45841301279477219 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1870
  constructor
  · exact (show ((22920650639738607 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((5684321358655174807 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((935 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((2842160679327587405 / 9223372036854775808 : ℚ) : ℝ) ≤ ((45841301279477219 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1871 : ((5596194124389761827 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1871 / 64 : ℚ) : ℝ) ∧
    heightZ ((1871 / 64 : ℚ) : ℝ) ≤ ((2798097062194880915 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((5596194124389761827 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1871 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((115 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((1871 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((115 / 192 : ℚ) : ℝ) ≤ ((2798097062194880915 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1871 : ((22565298888668393 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((1871 / 64 : ℚ) : ℝ) ∧
    logKernel ((1871 / 64 : ℚ) : ℝ) ≤ ((45130597777336791 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1871
  constructor
  · exact (show ((22565298888668393 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((5596194124389761827 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1871 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((2798097062194880915 / 9223372036854775808 : ℚ) : ℝ) ≤ ((45130597777336791 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1872 : ((344339573515770113 / 1152921504606846976 : ℚ) : ℝ) ≤ heightZ ((117 / 4 : ℚ) : ℝ) ∧
    heightZ ((117 / 4 : ℚ) : ℝ) ≤ ((5509433176252321811 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((344339573515770113 / 1152921504606846976 : ℚ) : ℝ) ≤ Real.exp (-((117 / 4 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((7 / 12 : ℚ) : ℝ) ∧
      Real.exp (-((117 / 4 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((7 / 12 : ℚ) : ℝ) ≤ ((5509433176252321811 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1872 : ((22215456355856135 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((117 / 4 : ℚ) : ℝ) ∧
    logKernel ((117 / 4 : ℚ) : ℝ) ≤ ((44430912711712275 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1872
  constructor
  · exact (show ((22215456355856135 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((344339573515770113 / 1152921504606846976 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((117 / 4 : ℚ) : ℝ)) hh).trans
      (show zKernel ((5509433176252321811 / 18446744073709551616 : ℚ) : ℝ) ≤ ((44430912711712275 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1873 : ((1356004332984950271 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((1873 / 64 : ℚ) : ℝ) ∧
    heightZ ((1873 / 64 : ℚ) : ℝ) ≤ ((5424017331939801087 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((1356004332984950271 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((1873 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((109 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((1873 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((109 / 192 : ℚ) : ℝ) ≤ ((5424017331939801087 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1873 : ((43742075257579039 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1873 / 64 : ℚ) : ℝ) ∧
    logKernel ((1873 / 64 : ℚ) : ℝ) ≤ ((10935518814394761 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1873
  constructor
  · exact (show ((43742075257579039 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((1356004332984950271 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1873 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((5424017331939801087 / 18446744073709551616 : ℚ) : ℝ) ≤ ((10935518814394761 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem log_height_bounds_0 : ((242093637687971423 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((921 / 32 : ℚ) : ℝ) ∧
    Real.log ((921 / 32 : ℚ) : ℝ) ≤ ((121046818843985713 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((242093637687971423 / 72057594037927936 : ℚ) : ℝ) ≤ ((921 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((921 / 32 : ℚ) : ℝ) ≤ Real.exp ((121046818843985713 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_0 : heightPower (0 : Fin 988) ≤ ((6142020705 / 17592186044416 : ℚ) : ℝ) := by
  have hh := log_height_bounds_0
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_0 : heightFactor (0 : Fin 988) ≤ ((6842520084211003 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_0
  obtain ⟨hpl, hph⟩ := kernel_bounds_1841
  obtain ⟨hcl, hch⟩ := kernel_bounds_1842
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1842
  have h : (((848241 / 512 : ℚ) : ℝ) * (logKernel ((1841 / 64 : ℚ) : ℝ) - logKernel ((921 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((921 / 32 : ℚ) : ℝ) + Real.log ((921 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((6842520084211003 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_1 : ((242132746288137907 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1843 / 64 : ℚ) : ℝ) ∧
    Real.log ((1843 / 64 : ℚ) : ℝ) ≤ ((121066373144068955 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((242132746288137907 / 72057594037927936 : ℚ) : ℝ) ≤ ((1843 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1843 / 64 : ℚ) : ℝ) ≤ Real.exp ((121066373144068955 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_1 : heightPower (1 : Fin 988) ≤ ((581135851473 / 35184372088832 : ℚ) : ℝ) := by
  have hh := log_height_bounds_1
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_1 : heightFactor (1 : Fin 988) ≤ ((7170742158077399 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_1
  obtain ⟨hpl, hph⟩ := kernel_bounds_1842
  obtain ⟨hcl, hch⟩ := kernel_bounds_1843
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1843
  have h : (((3396649 / 2048 : ℚ) : ℝ) * (logKernel ((921 / 32 : ℚ) : ℝ) - logKernel ((1843 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1843 / 64 : ℚ) : ℝ) + Real.log ((1843 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((7170742158077399 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_2 : ((242171833673982675 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((461 / 16 : ℚ) : ℝ) ∧
    Real.log ((461 / 16 : ℚ) : ℝ) ≤ ((121085916836991339 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((242171833673982675 / 72057594037927936 : ℚ) : ℝ) ≤ ((461 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((461 / 16 : ℚ) : ℝ) ≤ Real.exp ((121085916836991339 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_2 : heightPower (2 : Fin 988) ≤ ((2299954605961 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_2
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_2 : heightFactor (2 : Fin 988) ≤ ((3552711160524609 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_2
  obtain ⟨hpl, hph⟩ := kernel_bounds_1843
  obtain ⟨hcl, hch⟩ := kernel_bounds_1844
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1844
  have h : (((212521 / 128 : ℚ) : ℝ) * (logKernel ((1843 / 64 : ℚ) : ℝ) - logKernel ((461 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((461 / 16 : ℚ) : ℝ) + Real.log ((461 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((3552711160524609 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_3 : ((60552724967127129 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((1845 / 64 : ℚ) : ℝ) ∧
    Real.log ((1845 / 64 : ℚ) : ℝ) ≤ ((242210899868508519 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((60552724967127129 / 18014398509481984 : ℚ) : ℝ) ≤ ((1845 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1845 / 64 : ℚ) : ℝ) ≤ Real.exp ((242210899868508519 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_3 : heightPower (3 : Fin 988) ≤ ((13750467257315 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_3
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_3 : heightFactor (3 : Fin 988) ≤ ((7040692665133027 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_3
  obtain ⟨hpl, hph⟩ := kernel_bounds_1844
  obtain ⟨hcl, hch⟩ := kernel_bounds_1845
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1845
  have h : (((3404025 / 2048 : ℚ) : ℝ) * (logKernel ((461 / 16 : ℚ) : ℝ) - logKernel ((1845 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1845 / 64 : ℚ) : ℝ) + Real.log ((1845 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((7040692665133027 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_4 : ((242249944894680827 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((923 / 32 : ℚ) : ℝ) ∧
    Real.log ((923 / 32 : ℚ) : ℝ) ≤ ((121124972447340415 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((242249944894680827 / 72057594037927936 : ℚ) : ℝ) ≤ ((923 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((923 / 32 : ℚ) : ℝ) ≤ Real.exp ((121124972447340415 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_4 : heightPower (4 : Fin 988) ≤ ((1143814587619 / 17592186044416 : ℚ) : ℝ) := by
  have hh := log_height_bounds_4
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_4 : heightFactor (4 : Fin 988) ≤ ((1744136976864951 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_4
  obtain ⟨hpl, hph⟩ := kernel_bounds_1845
  obtain ⟨hcl, hch⟩ := kernel_bounds_1846
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1846
  have h : (((851929 / 512 : ℚ) : ℝ) * (logKernel ((1845 / 64 : ℚ) : ℝ) - logKernel ((923 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((923 / 32 : ℚ) : ℝ) + Real.log ((923 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1744136976864951 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_5 : ((15143060548464231 / 4503599627370496 : ℚ) : ℝ) ≤ Real.log ((1847 / 64 : ℚ) : ℝ) ∧
    Real.log ((1847 / 64 : ℚ) : ℝ) ≤ ((242288968775427699 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((15143060548464231 / 4503599627370496 : ℚ) : ℝ) ≤ ((1847 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1847 / 64 : ℚ) : ℝ) ≤ Real.exp ((242288968775427699 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_5 : heightPower (5 : Fin 988) ≤ ((2856439618397 / 35184372088832 : ℚ) : ℝ) := by
  have hh := log_height_bounds_5
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_5 : heightFactor (5 : Fin 988) ≤ ((3456491405969977 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_5
  obtain ⟨hpl, hph⟩ := kernel_bounds_1846
  obtain ⟨hcl, hch⟩ := kernel_bounds_1847
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1847
  have h : (((3411409 / 2048 : ℚ) : ℝ) * (logKernel ((923 / 32 : ℚ) : ℝ) - logKernel ((1847 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1847 / 64 : ℚ) : ℝ) + Real.log ((1847 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((3456491405969977 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_6 : ((242327971533639975 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((231 / 8 : ℚ) : ℝ) ∧
    Real.log ((231 / 8 : ℚ) : ℝ) ≤ ((121163985766819989 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((242327971533639975 / 72057594037927936 : ℚ) : ℝ) ≤ ((231 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((231 / 8 : ℚ) : ℝ) ≤ Real.exp ((121163985766819989 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_6 : heightPower (6 : Fin 988) ≤ ((27401917982547 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_6
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_6 : heightFactor (6 : Fin 988) ≤ ((6849992188854311 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_6
  obtain ⟨hpl, hph⟩ := kernel_bounds_1847
  obtain ⟨hcl, hch⟩ := kernel_bounds_1848
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1848
  have h : (((53361 / 32 : ℚ) : ℝ) * (logKernel ((1847 / 64 : ℚ) : ℝ) - logKernel ((231 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((231 / 8 : ℚ) : ℝ) + Real.log ((231 / 8 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((6849992188854311 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_7 : ((121183476596085685 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((1849 / 64 : ℚ) : ℝ) ∧
    Real.log ((1849 / 64 : ℚ) : ℝ) ≤ ((242366953192171373 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((121183476596085685 / 36028797018963968 : ℚ) : ℝ) ≤ ((1849 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1849 / 64 : ℚ) : ℝ) ≤ Real.exp ((242366953192171373 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_7 : heightPower (7 : Fin 988) ≤ ((31952236597289 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_7
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_7 : heightFactor (7 : Fin 988) ≤ ((6787570894448663 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_7
  obtain ⟨hpl, hph⟩ := kernel_bounds_1848
  obtain ⟨hcl, hch⟩ := kernel_bounds_1849
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1849
  have h : (((3418801 / 2048 : ℚ) : ℝ) * (logKernel ((231 / 8 : ℚ) : ℝ) - logKernel ((1849 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1849 / 64 : ℚ) : ℝ) + Real.log ((1849 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((6787570894448663 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_8 : ((121202956886919257 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((925 / 32 : ℚ) : ℝ) ∧
    Real.log ((925 / 32 : ℚ) : ℝ) ≤ ((242405913773838517 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((121202956886919257 / 36028797018963968 : ℚ) : ℝ) ≤ ((925 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((925 / 32 : ℚ) : ℝ) ≤ Real.exp ((242405913773838517 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_8 : heightPower (8 : Fin 988) ≤ ((18251236440265 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_8
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_8 : heightFactor (8 : Fin 988) ≤ ((6725713830531775 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_8
  obtain ⟨hpl, hph⟩ := kernel_bounds_1849
  obtain ⟨hcl, hch⟩ := kernel_bounds_1850
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1850
  have h : (((855625 / 512 : ℚ) : ℝ) * (logKernel ((1849 / 64 : ℚ) : ℝ) - logKernel ((925 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((925 / 32 : ℚ) : ℝ) + Real.log ((925 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((6725713830531775 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_9 : ((242444853301421053 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1851 / 64 : ℚ) : ℝ) ∧
    Real.log ((1851 / 64 : ℚ) : ℝ) ≤ ((236762552052169 / 70368744177664 : ℚ) : ℝ) := by
  have hl : Real.exp ((242444853301421053 / 72057594037927936 : ℚ) : ℝ) ≤ ((1851 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1851 / 64 : ℚ) : ℝ) ≤ Real.exp ((236762552052169 / 70368744177664 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_9 : heightPower (9 : Fin 988) ≤ ((41052626921253 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_9
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_9 : heightFactor (9 : Fin 988) ≤ ((6664415944076869 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_9
  obtain ⟨hpl, hph⟩ := kernel_bounds_1850
  obtain ⟨hcl, hch⟩ := kernel_bounds_1851
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1851
  have h : (((3426201 / 2048 : ℚ) : ℝ) * (logKernel ((925 / 32 : ℚ) : ℝ) - logKernel ((1851 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1851 / 64 : ℚ) : ℝ) + Real.log ((1851 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((6664415944076869 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_10 : ((242483771797661719 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((463 / 16 : ℚ) : ℝ) ∧
    Real.log ((463 / 16 : ℚ) : ℝ) ≤ ((121241885898830861 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((242483771797661719 / 72057594037927936 : ℚ) : ℝ) ≤ ((463 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((463 / 16 : ℚ) : ℝ) ≤ Real.exp ((121241885898830861 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_10 : heightPower (10 : Fin 988) ≤ ((22801349404149 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_10
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_10 : heightFactor (10 : Fin 988) ≤ ((6603672226826537 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_10
  obtain ⟨hpl, hph⟩ := kernel_bounds_1851
  obtain ⟨hcl, hch⟩ := kernel_bounds_1852
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1852
  have h : (((214369 / 128 : ℚ) : ℝ) * (logKernel ((1851 / 64 : ℚ) : ℝ) - logKernel ((463 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((463 / 16 : ℚ) : ℝ) + Real.log ((463 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((6603672226826537 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_11 : ((15157666830329151 / 4503599627370496 : ℚ) : ℝ) ≤ Real.log ((1853 / 64 : ℚ) : ℝ) ∧
    Real.log ((1853 / 64 : ℚ) : ℝ) ≤ ((242522669285266419 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((15157666830329151 / 4503599627370496 : ℚ) : ℝ) ≤ ((1853 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1853 / 64 : ℚ) : ℝ) ≤ Real.exp ((242522669285266419 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_11 : heightPower (11 : Fin 988) ≤ ((50152688630357 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_11
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_11 : heightFactor (11 : Fin 988) ≤ ((1635869428725265 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_11
  obtain ⟨hpl, hph⟩ := kernel_bounds_1852
  obtain ⟨hcl, hch⟩ := kernel_bounds_1853
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1853
  have h : (((3433609 / 2048 : ℚ) : ℝ) * (logKernel ((463 / 16 : ℚ) : ℝ) - logKernel ((1853 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1853 / 64 : ℚ) : ℝ) + Real.log ((1853 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1635869428725265 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_12 : ((242561545786904299 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((927 / 32 : ℚ) : ℝ) ∧
    Real.log ((927 / 32 : ℚ) : ℝ) ≤ ((121280772893452151 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((242561545786904299 / 72057594037927936 : ℚ) : ℝ) ≤ ((927 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((927 / 32 : ℚ) : ℝ) ≤ Real.exp ((121280772893452151 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_12 : heightPower (12 : Fin 988) ≤ ((3418912279749 / 17592186044416 : ℚ) : ℝ) := by
  have hh := log_height_bounds_12
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_12 : heightFactor (12 : Fin 988) ≤ ((1620956872102527 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_12
  obtain ⟨hpl, hph⟩ := kernel_bounds_1853
  obtain ⟨hcl, hch⟩ := kernel_bounds_1854
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1854
  have h : (((859329 / 512 : ℚ) : ℝ) * (logKernel ((1853 / 64 : ℚ) : ℝ) - logKernel ((927 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((927 / 32 : ℚ) : ℝ) + Real.log ((927 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1620956872102527 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_13 : ((242600401325207847 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1855 / 64 : ℚ) : ℝ) ∧
    Real.log ((1855 / 64 : ℚ) : ℝ) ≤ ((121300200662603925 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((242600401325207847 / 72057594037927936 : ℚ) : ℝ) ≤ ((1855 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1855 / 64 : ℚ) : ℝ) ≤ Real.exp ((121300200662603925 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_13 : heightPower (13 : Fin 988) ≤ ((59252422433587 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_13
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_13 : heightFactor (13 : Fin 988) ≤ ((1606179167766943 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_13
  obtain ⟨hpl, hph⟩ := kernel_bounds_1854
  obtain ⟨hcl, hch⟩ := kernel_bounds_1855
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1855
  have h : (((3441025 / 2048 : ℚ) : ℝ) * (logKernel ((927 / 32 : ℚ) : ℝ) - logKernel ((1855 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1855 / 64 : ℚ) : ℝ) + Real.log ((1855 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1606179167766943 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_14 : ((121319617961386475 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((29 / 1 : ℚ) : ℝ) ∧
    Real.log ((29 / 1 : ℚ) : ℝ) ≤ ((242639235922772953 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((121319617961386475 / 36028797018963968 : ℚ) : ℝ) ≤ ((29 / 1 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((29 / 1 : ℚ) : ℝ) ≤ Real.exp ((242639235922772953 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_14 : heightPower (14 : Fin 988) ≤ ((63802166591429 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_14
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_14 : heightFactor (14 : Fin 988) ≤ ((3183070214905467 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_14
  obtain ⟨hpl, hph⟩ := kernel_bounds_1855
  obtain ⟨hcl, hch⟩ := kernel_bounds_1856
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1856
  have h : (((1682 / 1 : ℚ) : ℝ) * (logKernel ((1855 / 64 : ℚ) : ℝ) - logKernel ((29 / 1 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((29 / 1 : ℚ) : ℝ) + Real.log ((29 / 1 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((3183070214905467 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_15 : ((242678049602158983 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1857 / 64 : ℚ) : ℝ) ∧
    Real.log ((1857 / 64 : ℚ) : ℝ) ≤ ((121339024801079493 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((242678049602158983 / 72057594037927936 : ℚ) : ℝ) ≤ ((1857 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1857 / 64 : ℚ) : ℝ) ≤ Real.exp ((121339024801079493 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_15 : heightPower (15 : Fin 988) ≤ ((68351829037635 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_15
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_15 : heightFactor (15 : Fin 988) ≤ ((394255873401307 / 17592186044416 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_15
  obtain ⟨hpl, hph⟩ := kernel_bounds_1856
  obtain ⟨hcl, hch⟩ := kernel_bounds_1857
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1857
  have h : (((3448449 / 2048 : ℚ) : ℝ) * (logKernel ((29 / 1 : ℚ) : ℝ) - logKernel ((1857 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1857 / 64 : ℚ) : ℝ) + Real.log ((1857 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((394255873401307 / 17592186044416 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_16 : ((121358421192944443 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((929 / 32 : ℚ) : ℝ) ∧
    Real.log ((929 / 32 : ℚ) : ℝ) ≤ ((242716842385888889 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((121358421192944443 / 36028797018963968 : ℚ) : ℝ) ≤ ((929 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((929 / 32 : ℚ) : ℝ) ≤ Real.exp ((242716842385888889 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_16 : heightPower (16 : Fin 988) ≤ ((9112676232523 / 35184372088832 : ℚ) : ℝ) := by
  have hh := log_height_bounds_16
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_16 : heightFactor (16 : Fin 988) ≤ ((6250572557148375 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_16
  obtain ⟨hpl, hph⟩ := kernel_bounds_1857
  obtain ⟨hcl, hch⟩ := kernel_bounds_1858
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1858
  have h : (((863041 / 512 : ℚ) : ℝ) * (logKernel ((1857 / 64 : ℚ) : ℝ) - logKernel ((929 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((929 / 32 : ℚ) : ℝ) + Real.log ((929 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((6250572557148375 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_17 : ((242755614296449243 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1859 / 64 : ℚ) : ℝ) ∧
    Real.log ((1859 / 64 : ℚ) : ℝ) ≤ ((121377807148224623 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((242755614296449243 / 72057594037927936 : ℚ) : ℝ) ≤ ((1859 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1859 / 64 : ℚ) : ℝ) ≤ Real.exp ((121377807148224623 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_17 : heightPower (17 : Fin 988) ≤ ((38725454573457 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_17
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_17 : heightFactor (17 : Fin 988) ≤ ((1548392868085373 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_17
  obtain ⟨hpl, hph⟩ := kernel_bounds_1858
  obtain ⟨hcl, hch⟩ := kernel_bounds_1859
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1859
  have h : (((3455881 / 2048 : ℚ) : ℝ) * (logKernel ((929 / 32 : ℚ) : ℝ) - logKernel ((1859 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1859 / 64 : ℚ) : ℝ) + Real.log ((1859 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1548392868085373 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_18 : ((121397182678145179 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((465 / 16 : ℚ) : ℝ) ∧
    Real.log ((465 / 16 : ℚ) : ℝ) ≤ ((242794365356290361 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((121397182678145179 / 36028797018963968 : ℚ) : ℝ) ≤ ((465 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((465 / 16 : ℚ) : ℝ) ≤ Real.exp ((242794365356290361 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_18 : heightPower (18 : Fin 988) ≤ ((82000326985523 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_18
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_18 : heightFactor (18 : Fin 988) ≤ ((6137086056077289 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_18
  obtain ⟨hpl, hph⟩ := kernel_bounds_1859
  obtain ⟨hcl, hch⟩ := kernel_bounds_1860
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1860
  have h : (((216225 / 128 : ℚ) : ℝ) * (logKernel ((1859 / 64 : ℚ) : ℝ) - logKernel ((465 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((465 / 16 : ℚ) : ℝ) + Real.log ((465 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((6137086056077289 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_19 : ((7588534237119573 / 2251799813685248 : ℚ) : ℝ) ≤ Real.log ((1861 / 64 : ℚ) : ℝ) ∧
    Real.log ((1861 / 64 : ℚ) : ℝ) ≤ ((242833095587826339 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((7588534237119573 / 2251799813685248 : ℚ) : ℝ) ≤ ((1861 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1861 / 64 : ℚ) : ℝ) ≤ Real.exp ((242833095587826339 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_19 : heightPower (19 : Fin 988) ≤ ((21637415865891 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_19
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_19 : heightFactor (19 : Fin 988) ≤ ((760138960724523 / 35184372088832 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_19
  obtain ⟨hpl, hph⟩ := kernel_bounds_1860
  obtain ⟨hcl, hch⟩ := kernel_bounds_1861
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1861
  have h : (((3463321 / 2048 : ℚ) : ℝ) * (logKernel ((465 / 16 : ℚ) : ℝ) - logKernel ((1861 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1861 / 64 : ℚ) : ℝ) + Real.log ((1861 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((760138960724523 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_20 : ((242871805013435159 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((931 / 32 : ℚ) : ℝ) ∧
    Real.log ((931 / 32 : ℚ) : ℝ) ≤ ((121435902506717581 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((242871805013435159 / 72057594037927936 : ℚ) : ℝ) ≤ ((931 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((931 / 32 : ℚ) : ℝ) ≤ Real.exp ((121435902506717581 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_20 : heightPower (20 : Fin 988) ≤ ((91098918668453 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_20
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_20 : heightFactor (20 : Fin 988) ≤ ((3012821889969839 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_20
  obtain ⟨hpl, hph⟩ := kernel_bounds_1861
  obtain ⟨hcl, hch⟩ := kernel_bounds_1862
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1862
  have h : (((866761 / 512 : ℚ) : ℝ) * (logKernel ((1861 / 64 : ℚ) : ℝ) - logKernel ((931 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((931 / 32 : ℚ) : ℝ) + Real.log ((931 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((3012821889969839 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_21 : ((242910493655458763 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1863 / 64 : ℚ) : ℝ) ∧
    Real.log ((1863 / 64 : ℚ) : ℝ) ≤ ((121455246827729383 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((242910493655458763 / 72057594037927936 : ℚ) : ℝ) ≤ ((1863 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1863 / 64 : ℚ) : ℝ) ≤ Real.exp ((121455246827729383 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_21 : heightPower (21 : Fin 988) ≤ ((95648092687461 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_21
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_21 : heightFactor (21 : Fin 988) ≤ ((5970677797591173 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_21
  obtain ⟨hpl, hph⟩ := kernel_bounds_1862
  obtain ⟨hcl, hch⟩ := kernel_bounds_1863
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1863
  have h : (((3470769 / 2048 : ℚ) : ℝ) * (logKernel ((931 / 32 : ℚ) : ℝ) - logKernel ((1863 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1863 / 64 : ℚ) : ℝ) + Real.log ((1863 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((5970677797591173 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_22 : ((242949161536203119 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((233 / 8 : ℚ) : ℝ) ∧
    Real.log ((233 / 8 : ℚ) : ℝ) ≤ ((121474580768101561 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((242949161536203119 / 72057594037927936 : ℚ) : ℝ) ≤ ((233 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((233 / 8 : ℚ) : ℝ) ≤ Real.exp ((121474580768101561 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_22 : heightPower (22 : Fin 988) ≤ ((100197185607723 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_22
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_22 : heightFactor (22 : Fin 988) ≤ ((369763077382493 / 17592186044416 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_22
  obtain ⟨hpl, hph⟩ := kernel_bounds_1863
  obtain ⟨hcl, hch⟩ := kernel_bounds_1864
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1864
  have h : (((54289 / 32 : ℚ) : ℝ) * (logKernel ((1863 / 64 : ℚ) : ℝ) - logKernel ((233 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((233 / 8 : ℚ) : ℝ) + Real.log ((233 / 8 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((369763077382493 / 17592186044416 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_23 : ((242987808677938303 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1865 / 64 : ℚ) : ℝ) ∧
    Real.log ((1865 / 64 : ℚ) : ℝ) ≤ ((121493904338969153 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((242987808677938303 / 72057594037927936 : ℚ) : ℝ) ≤ ((1865 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1865 / 64 : ℚ) : ℝ) ≤ Real.exp ((121493904338969153 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_23 : heightPower (23 : Fin 988) ≤ ((52373098758115 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_23
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_23 : heightFactor (23 : Fin 988) ≤ ((5862233640827855 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_23
  obtain ⟨hpl, hph⟩ := kernel_bounds_1864
  obtain ⟨hcl, hch⟩ := kernel_bounds_1865
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1865
  have h : (((3478225 / 2048 : ℚ) : ℝ) * (logKernel ((233 / 8 : ℚ) : ℝ) - logKernel ((1865 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1865 / 64 : ℚ) : ℝ) + Real.log ((1865 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((5862233640827855 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_24 : ((121513217551449291 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((933 / 32 : ℚ) : ℝ) ∧
    Real.log ((933 / 32 : ℚ) : ℝ) ≤ ((243026435102898585 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((121513217551449291 / 36028797018963968 : ℚ) : ℝ) ≤ ((933 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((933 / 32 : ℚ) : ℝ) ≤ Real.exp ((243026435102898585 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_24 : heightPower (24 : Fin 988) ≤ ((109295128499835 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_24
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_24 : heightFactor (24 : Fin 988) ≤ ((5808746584599951 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_24
  obtain ⟨hpl, hph⟩ := kernel_bounds_1865
  obtain ⟨hcl, hch⟩ := kernel_bounds_1866
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1866
  have h : (((870489 / 512 : ℚ) : ℝ) * (logKernel ((1865 / 64 : ℚ) : ℝ) - logKernel ((933 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((933 / 32 : ℚ) : ℝ) + Real.log ((933 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((5808746584599951 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_25 : ((60766260208320621 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((1867 / 64 : ℚ) : ℝ) ∧
    Real.log ((1867 / 64 : ℚ) : ℝ) ≤ ((243065040833282487 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((60766260208320621 / 18014398509481984 : ℚ) : ℝ) ≤ ((1867 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1867 / 64 : ℚ) : ℝ) ≤ Real.exp ((243065040833282487 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_25 : heightPower (25 : Fin 988) ≤ ((113843978645251 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_25
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_25 : heightFactor (25 : Fin 988) ≤ ((5755743687556965 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_25
  obtain ⟨hpl, hph⟩ := kernel_bounds_1866
  obtain ⟨hcl, hch⟩ := kernel_bounds_1867
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1867
  have h : (((3485689 / 2048 : ℚ) : ℝ) * (logKernel ((933 / 32 : ℚ) : ℝ) - logKernel ((1867 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1867 / 64 : ℚ) : ℝ) + Real.log ((1867 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((5755743687556965 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_26 : ((243103625891252875 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((467 / 16 : ℚ) : ℝ) ∧
    Real.log ((467 / 16 : ℚ) : ℝ) ≤ ((121551812945626439 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((243103625891252875 / 72057594037927936 : ℚ) : ℝ) ≤ ((467 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((467 / 16 : ℚ) : ℝ) ≤ Real.exp ((121551812945626439 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_26 : heightPower (26 : Fin 988) ≤ ((29598187009763 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_26
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_26 : heightFactor (26 : Fin 988) ≤ ((5703220606711657 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_26
  obtain ⟨hpl, hph⟩ := kernel_bounds_1867
  obtain ⟨hcl, hch⟩ := kernel_bounds_1868
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1868
  have h : (((218089 / 128 : ℚ) : ℝ) * (logKernel ((1867 / 64 : ℚ) : ℝ) - logKernel ((467 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((467 / 16 : ℚ) : ℝ) + Real.log ((467 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((5703220606711657 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_27 : ((243142190298937041 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1869 / 64 : ℚ) : ℝ) ∧
    Real.log ((1869 / 64 : ℚ) : ℝ) ≤ ((60785547574734261 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((243142190298937041 / 72057594037927936 : ℚ) : ℝ) ≤ ((1869 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1869 / 64 : ℚ) : ℝ) ≤ Real.exp ((60785547574734261 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_27 : heightPower (27 : Fin 988) ≤ ((15367679595959 / 35184372088832 : ℚ) : ℝ) := by
  have hh := log_height_bounds_27
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_27 : heightFactor (27 : Fin 988) ≤ ((5651173037627783 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_27
  obtain ⟨hpl, hph⟩ := kernel_bounds_1868
  obtain ⟨hcl, hch⟩ := kernel_bounds_1869
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1869
  have h : (((3493161 / 2048 : ℚ) : ℝ) * (logKernel ((467 / 16 : ℚ) : ℝ) - logKernel ((1869 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1869 / 64 : ℚ) : ℝ) + Real.log ((1869 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((5651173037627783 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_28 : ((121590367039213379 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((935 / 32 : ℚ) : ℝ) ∧
    Real.log ((935 / 32 : ℚ) : ℝ) ≤ ((243180734078426761 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((121590367039213379 / 36028797018963968 : ℚ) : ℝ) ≤ ((935 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((935 / 32 : ℚ) : ℝ) ≤ Real.exp ((243180734078426761 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_28 : heightPower (28 : Fin 988) ≤ ((3984063903669 / 8796093022208 : ℚ) : ℝ) := by
  have hh := log_height_bounds_28
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_28 : heightFactor (28 : Fin 988) ≤ ((2799798357041037 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_28
  obtain ⟨hpl, hph⟩ := kernel_bounds_1869
  obtain ⟨hcl, hch⟩ := kernel_bounds_1870
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1870
  have h : (((874225 / 512 : ℚ) : ℝ) * (logKernel ((1869 / 64 : ℚ) : ℝ) - logKernel ((935 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((935 / 32 : ℚ) : ℝ) + Real.log ((935 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((2799798357041037 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_29 : ((3800300894559037 / 1125899906842624 : ℚ) : ℝ) ≤ Real.log ((1871 / 64 : ℚ) : ℝ) ∧
    Real.log ((1871 / 64 : ℚ) : ℝ) ≤ ((243219257251778371 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((3800300894559037 / 1125899906842624 : ℚ) : ℝ) ≤ ((1871 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1871 / 64 : ℚ) : ℝ) ≤ Real.exp ((243219257251778371 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_29 : heightPower (29 : Fin 988) ≤ ((132038572574417 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_29
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_29 : heightFactor (29 : Fin 988) ≤ ((5548487407729129 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_29
  obtain ⟨hpl, hph⟩ := kernel_bounds_1870
  obtain ⟨hcl, hch⟩ := kernel_bounds_1871
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1871
  have h : (((3500641 / 2048 : ℚ) : ℝ) * (logKernel ((935 / 32 : ℚ) : ℝ) - logKernel ((1871 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1871 / 64 : ℚ) : ℝ) + Real.log ((1871 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((5548487407729129 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_30 : ((121628879920506431 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((117 / 4 : ℚ) : ℝ) ∧
    Real.log ((117 / 4 : ℚ) : ℝ) ≤ ((243257759841012865 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((121628879920506431 / 36028797018963968 : ℚ) : ℝ) ≤ ((117 / 4 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((117 / 4 : ℚ) : ℝ) ≤ Real.exp ((243257759841012865 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_30 : heightPower (30 : Fin 988) ≤ ((68293509912359 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_30
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_30 : heightFactor (30 : Fin 988) ≤ ((2748920463884605 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_30
  obtain ⟨hpl, hph⟩ := kernel_bounds_1871
  obtain ⟨hcl, hch⟩ := kernel_bounds_1872
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1872
  have h : (((13689 / 8 : ℚ) : ℝ) * (logKernel ((1871 / 64 : ℚ) : ℝ) - logKernel ((117 / 4 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((117 / 4 : ℚ) : ℝ) + Real.log ((117 / 4 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((2748920463884605 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_31 : ((243296241868115945 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1873 / 64 : ℚ) : ℝ) ∧
    Real.log ((1873 / 64 : ℚ) : ℝ) ≤ ((60824060467028987 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((243296241868115945 / 72057594037927936 : ℚ) : ℝ) ≤ ((1873 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1873 / 64 : ℚ) : ℝ) ≤ Real.exp ((60824060467028987 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_31 : heightPower (31 : Fin 988) ≤ ((141135386754193 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_31
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_31 : heightFactor (31 : Fin 988) ≤ ((2723826560309451 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_31
  obtain ⟨hpl, hph⟩ := kernel_bounds_1872
  obtain ⟨hcl, hch⟩ := kernel_bounds_1873
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1873
  have h : (((3508129 / 2048 : ℚ) : ℝ) * (logKernel ((117 / 4 : ℚ) : ℝ) - logKernel ((1873 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1873 / 64 : ℚ) : ℝ) + Real.log ((1873 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((2723826560309451 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

end LegendreK6.M2Pilot.Enclosures.Height000
