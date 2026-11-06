import LegendreK6.M2PilotDefinitions
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp

/-! Generated proposals: every bound is checked by Lean, not by trusting Arb. -/
namespace LegendreK6.M2Pilot.Enclosures.Height010
set_option maxRecDepth 100000
set_option maxHeartbeats 0

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

theorem height_z_bounds_2162 : ((14830304133229363 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((1081 / 32 : ℚ) : ℝ) ∧
    heightZ ((1081 / 32 : ℚ) : ℝ) ≤ ((59321216532917455 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((14830304133229363 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((1081 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-379 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1081 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-379 / 96 : ℚ) : ℝ) ≤ ((59321216532917455 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2162 : ((12307466911877 / 9007199254740992 : ℚ) : ℝ) ≤ logKernel ((1081 / 32 : ℚ) : ℝ) ∧
    logKernel ((1081 / 32 : ℚ) : ℝ) ≤ ((98459735295021 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2162
  constructor
  · exact (show ((12307466911877 / 9007199254740992 : ℚ) : ℝ) ≤ zKernel ((14830304133229363 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1081 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((59321216532917455 / 18446744073709551616 : ℚ) : ℝ) ≤ ((98459735295021 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2163 : ((58401526315483557 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2163 / 64 : ℚ) : ℝ) ∧
    heightZ ((2163 / 64 : ℚ) : ℝ) ≤ ((7300190789435445 / 2305843009213693952 : ℚ) : ℝ) := by
  have h : ((58401526315483557 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2163 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-761 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2163 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-761 / 192 : ℚ) : ℝ) ≤ ((7300190789435445 / 2305843009213693952 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2163 : ((95430447705673 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2163 / 64 : ℚ) : ℝ) ∧
    logKernel ((2163 / 64 : ℚ) : ℝ) ≤ ((47715223852839 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2163
  constructor
  · exact (show ((95430447705673 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((58401526315483557 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2163 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((7300190789435445 / 2305843009213693952 : ℚ) : ℝ) ≤ ((47715223852839 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2164 : ((57496094573271159 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((541 / 16 : ℚ) : ℝ) ∧
    heightZ ((541 / 16 : ℚ) : ℝ) ≤ ((28748047286635581 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((57496094573271159 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((541 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-191 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((541 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-191 / 48 : ℚ) : ℝ) ≤ ((28748047286635581 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2164 : ((92494361497295 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((541 / 16 : ℚ) : ℝ) ∧
    logKernel ((541 / 16 : ℚ) : ℝ) ≤ ((23123590374325 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2164
  constructor
  · exact (show ((92494361497295 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((57496094573271159 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((541 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((28748047286635581 / 9223372036854775808 : ℚ) : ℝ) ≤ ((23123590374325 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2165 : ((28302350124555727 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2165 / 64 : ℚ) : ℝ) ∧
    heightZ ((2165 / 64 : ℚ) : ℝ) ≤ ((56604700249111457 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((28302350124555727 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2165 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-767 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2165 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-767 / 192 : ℚ) : ℝ) ≤ ((56604700249111457 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2165 : ((5603038072803 / 4503599627370496 : ℚ) : ℝ) ≤ logKernel ((2165 / 64 : ℚ) : ℝ) ∧
    logKernel ((2165 / 64 : ℚ) : ℝ) ≤ ((89648609164853 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2165
  constructor
  · exact (show ((5603038072803 / 4503599627370496 : ℚ) : ℝ) ≤ zKernel ((28302350124555727 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2165 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((56604700249111457 / 18446744073709551616 : ℚ) : ℝ) ≤ ((89648609164853 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2166 : ((13931781428252345 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((1083 / 32 : ℚ) : ℝ) ∧
    heightZ ((1083 / 32 : ℚ) : ℝ) ≤ ((55727125713009383 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((13931781428252345 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((1083 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-385 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1083 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-385 / 96 : ℚ) : ℝ) ≤ ((55727125713009383 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2166 : ((86890411427151 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1083 / 32 : ℚ) : ℝ) ∧
    logKernel ((1083 / 32 : ℚ) : ℝ) ≤ ((21722602856789 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2166
  constructor
  · exact (show ((86890411427151 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((13931781428252345 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1083 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((55727125713009383 / 18446744073709551616 : ℚ) : ℝ) ≤ ((21722602856789 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2167 : ((27431578354505107 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2167 / 64 : ℚ) : ℝ) ∧
    heightZ ((2167 / 64 : ℚ) : ℝ) ≤ ((54863156709010217 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((27431578354505107 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2167 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-773 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2167 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-773 / 192 : ℚ) : ℝ) ≤ ((54863156709010217 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2167 : ((42108537256259 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2167 / 64 : ℚ) : ℝ) ∧
    logKernel ((2167 / 64 : ℚ) : ℝ) ≤ ((84217074512523 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2167
  constructor
  · exact (show ((42108537256259 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((27431578354505107 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2167 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((54863156709010217 / 18446744073709551616 : ℚ) : ℝ) ≤ ((84217074512523 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2168 : ((13503145575722481 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((271 / 8 : ℚ) : ℝ) ∧
    heightZ ((271 / 8 : ℚ) : ℝ) ≤ ((54012582302889927 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((13503145575722481 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((271 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-97 / 24 : ℚ) : ℝ) ∧
      Real.exp (-((271 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-97 / 24 : ℚ) : ℝ) ≤ ((54012582302889927 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2168 : ((81625987527903 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((271 / 8 : ℚ) : ℝ) ∧
    logKernel ((271 / 8 : ℚ) : ℝ) ≤ ((20406496881977 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2168
  constructor
  · exact (show ((81625987527903 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((13503145575722481 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((271 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((54012582302889927 / 18446744073709551616 : ℚ) : ℝ) ≤ ((20406496881977 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2169 : ((53175194830656507 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2169 / 64 : ℚ) : ℝ) ∧
    heightZ ((2169 / 64 : ℚ) : ℝ) ≤ ((26587597415328255 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((53175194830656507 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2169 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-779 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2169 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-779 / 192 : ℚ) : ℝ) ≤ ((26587597415328255 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2169 : ((79114619908995 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2169 / 64 : ℚ) : ℝ) ∧
    logKernel ((2169 / 64 : ℚ) : ℝ) ≤ ((9889327488625 / 9007199254740992 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2169
  constructor
  · exact (show ((79114619908995 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((53175194830656507 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2169 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((26587597415328255 / 9223372036854775808 : ℚ) : ℝ) ≤ ((9889327488625 / 9007199254740992 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2170 : ((26175394923924871 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((1085 / 32 : ℚ) : ℝ) ∧
    heightZ ((1085 / 32 : ℚ) : ℝ) ≤ ((52350789847849745 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((26175394923924871 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((1085 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-391 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1085 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-391 / 96 : ℚ) : ℝ) ≤ ((52350789847849745 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2170 : ((38340259474381 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((1085 / 32 : ℚ) : ℝ) ∧
    logKernel ((1085 / 32 : ℚ) : ℝ) ≤ ((76680518948767 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2170
  constructor
  · exact (show ((38340259474381 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((26175394923924871 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1085 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((52350789847849745 / 18446744073709551616 : ℚ) : ℝ) ≤ ((76680518948767 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2171 : ((25769583039813489 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2171 / 64 : ℚ) : ℝ) ∧
    heightZ ((2171 / 64 : ℚ) : ℝ) ≤ ((51539166079626981 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((25769583039813489 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2171 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-785 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2171 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-785 / 192 : ℚ) : ℝ) ≤ ((51539166079626981 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2171 : ((74321307402033 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2171 / 64 : ℚ) : ℝ) ∧
    logKernel ((2171 / 64 : ℚ) : ℝ) ≤ ((37160653701019 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2171
  constructor
  · exact (show ((74321307402033 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((25769583039813489 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2171 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((51539166079626981 / 18446744073709551616 : ℚ) : ℝ) ≤ ((37160653701019 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2172 : ((50740125371622763 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((543 / 16 : ℚ) : ℝ) ∧
    heightZ ((543 / 16 : ℚ) : ℝ) ≤ ((25370062685811383 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((50740125371622763 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((543 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-197 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((543 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-197 / 48 : ℚ) : ℝ) ≤ ((25370062685811383 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2172 : ((72034681163783 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((543 / 16 : ℚ) : ℝ) ∧
    logKernel ((543 / 16 : ℚ) : ℝ) ≤ ((18008670290947 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2172
  constructor
  · exact (show ((72034681163783 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((50740125371622763 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((543 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((25370062685811383 / 9223372036854775808 : ℚ) : ℝ) ≤ ((18008670290947 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2173 : ((24976736320785167 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2173 / 64 : ℚ) : ℝ) ∧
    heightZ ((2173 / 64 : ℚ) : ℝ) ≤ ((49953472641570337 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((24976736320785167 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2173 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-791 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2173 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-791 / 192 : ℚ) : ℝ) ≤ ((49953472641570337 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2173 : ((69818407018845 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2173 / 64 : ℚ) : ℝ) ∧
    logKernel ((2173 / 64 : ℚ) : ℝ) ≤ ((34909203509425 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2173
  constructor
  · exact (show ((69818407018845 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((24976736320785167 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2173 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((49953472641570337 / 18446744073709551616 : ℚ) : ℝ) ≤ ((34909203509425 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2174 : ((12294753957918285 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((1087 / 32 : ℚ) : ℝ) ∧
    heightZ ((1087 / 32 : ℚ) : ℝ) ≤ ((49179015831673143 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((12294753957918285 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((1087 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-397 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1087 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-397 / 96 : ℚ) : ℝ) ≤ ((49179015831673143 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2174 : ((67670320460861 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1087 / 32 : ℚ) : ℝ) ∧
    logKernel ((1087 / 32 : ℚ) : ℝ) ≤ ((33835160230433 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2174
  constructor
  · exact (show ((67670320460861 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((12294753957918285 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1087 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((49179015831673143 / 18446744073709551616 : ℚ) : ℝ) ≤ ((33835160230433 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2175 : ((24208282930857389 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2175 / 64 : ℚ) : ℝ) ∧
    heightZ ((2175 / 64 : ℚ) : ℝ) ≤ ((48416565861714781 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((24208282930857389 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2175 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-797 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2175 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-797 / 192 : ℚ) : ℝ) ≤ ((48416565861714781 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2175 : ((65588323578331 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2175 / 64 : ℚ) : ℝ) ∧
    logKernel ((2175 / 64 : ℚ) : ℝ) ≤ ((2049635111823 / 2251799813685248 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2175
  constructor
  · exact (show ((65588323578331 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((24208282930857389 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2175 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((48416565861714781 / 18446744073709551616 : ℚ) : ℝ) ≤ ((2049635111823 / 2251799813685248 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2176 : ((47665936582895891 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((34 / 1 : ℚ) : ℝ) ∧
    heightZ ((34 / 1 : ℚ) : ℝ) ≤ ((23832968291447947 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((47665936582895891 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((34 / 1 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-25 / 6 : ℚ) : ℝ) ∧
      Real.exp (-((34 / 1 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-25 / 6 : ℚ) : ℝ) ≤ ((23832968291447947 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2176 : ((63570383005707 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((34 / 1 : ℚ) : ℝ) ∧
    logKernel ((34 / 1 : ℚ) : ℝ) ≤ ((3973148937857 / 4503599627370496 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2176
  constructor
  · exact (show ((63570383005707 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((47665936582895891 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((34 / 1 : ℚ) : ℝ)) hh).trans
      (show zKernel ((23832968291447947 / 9223372036854775808 : ℚ) : ℝ) ≤ ((3973148937857 / 4503599627370496 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2177 : ((11731736183096689 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((2177 / 64 : ℚ) : ℝ) ∧
    heightZ ((2177 / 64 : ℚ) : ℝ) ≤ ((46926944732386759 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((11731736183096689 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((2177 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-803 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2177 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-803 / 192 : ℚ) : ℝ) ≤ ((46926944732386759 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2177 : ((61614527937521 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2177 / 64 : ℚ) : ℝ) ∧
    logKernel ((2177 / 64 : ℚ) : ℝ) ≤ ((30807263968763 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2177
  constructor
  · exact (show ((61614527937521 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((11731736183096689 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2177 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((46926944732386759 / 18446744073709551616 : ℚ) : ℝ) ≤ ((30807263968763 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2178 : ((1443731559018265 / 576460752303423488 : ℚ) : ℝ) ≤ heightZ ((1089 / 32 : ℚ) : ℝ) ∧
    heightZ ((1089 / 32 : ℚ) : ℝ) ≤ ((46199409888584483 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((1443731559018265 / 576460752303423488 : ℚ) : ℝ) ≤ Real.exp (-((1089 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-403 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1089 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-403 / 96 : ℚ) : ℝ) ≤ ((46199409888584483 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2178 : ((59718848203617 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1089 / 32 : ℚ) : ℝ) ∧
    logKernel ((1089 / 32 : ℚ) : ℝ) ≤ ((29859424101811 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2178
  constructor
  · exact (show ((59718848203617 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((1443731559018265 / 576460752303423488 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1089 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((46199409888584483 / 18446744073709551616 : ℚ) : ℝ) ≤ ((29859424101811 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2179 : ((45483154427063853 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2179 / 64 : ℚ) : ℝ) ∧
    heightZ ((2179 / 64 : ℚ) : ℝ) ≤ ((2842697151691491 / 1152921504606846976 : ℚ) : ℝ) := by
  have h : ((45483154427063853 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2179 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-809 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2179 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-809 / 192 : ℚ) : ℝ) ≤ ((2842697151691491 / 1152921504606846976 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2179 : ((57881492403593 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2179 / 64 : ℚ) : ℝ) ∧
    logKernel ((2179 / 64 : ℚ) : ℝ) ≤ ((28940746201799 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2179
  constructor
  · exact (show ((57881492403593 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((45483154427063853 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2179 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((2842697151691491 / 1152921504606846976 : ℚ) : ℝ) ≤ ((28940746201799 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2180 : ((44778003477211131 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((545 / 16 : ℚ) : ℝ) ∧
    heightZ ((545 / 16 : ℚ) : ℝ) ≤ ((22389001738605567 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((44778003477211131 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((545 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-203 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((545 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-203 / 48 : ℚ) : ℝ) ≤ ((22389001738605567 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2180 : ((14025166524663 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((545 / 16 : ℚ) : ℝ) ∧
    logKernel ((545 / 16 : ℚ) : ℝ) ≤ ((56100666098657 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2180
  constructor
  · exact (show ((14025166524663 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((44778003477211131 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((545 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((22389001738605567 / 9223372036854775808 : ℚ) : ℝ) ≤ ((56100666098657 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2181 : ((22041892439765073 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2181 / 64 : ℚ) : ℝ) ∧
    heightZ ((2181 / 64 : ℚ) : ℝ) ≤ ((44083784879530149 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((22041892439765073 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2181 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-815 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2181 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-815 / 192 : ℚ) : ℝ) ≤ ((44083784879530149 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2181 : ((27187315029537 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2181 / 64 : ℚ) : ℝ) ∧
    logKernel ((2181 / 64 : ℚ) : ℝ) ≤ ((54374630059079 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2181
  constructor
  · exact (show ((27187315029537 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((22041892439765073 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2181 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((44083784879530149 / 18446744073709551616 : ℚ) : ℝ) ≤ ((54374630059079 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2182 : ((21700164571805163 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((1091 / 32 : ℚ) : ℝ) ∧
    heightZ ((1091 / 32 : ℚ) : ℝ) ≤ ((43400329143610329 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((21700164571805163 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((1091 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-409 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1091 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-409 / 96 : ℚ) : ℝ) ≤ ((43400329143610329 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2182 : ((52701698565611 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1091 / 32 : ℚ) : ℝ) ∧
    logKernel ((1091 / 32 : ℚ) : ℝ) ≤ ((3293856160351 / 4503599627370496 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2182
  constructor
  · exact (show ((52701698565611 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((21700164571805163 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1091 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((43400329143610329 / 18446744073709551616 : ℚ) : ℝ) ≤ ((3293856160351 / 4503599627370496 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2183 : ((21363734703373177 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2183 / 64 : ℚ) : ℝ) ∧
    heightZ ((2183 / 64 : ℚ) : ℝ) ≤ ((42727469406746357 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((21363734703373177 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2183 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-821 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2183 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-821 / 192 : ℚ) : ℝ) ≤ ((42727469406746357 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2183 : ((6385029720393 / 9007199254740992 : ℚ) : ℝ) ≤ logKernel ((2183 / 64 : ℚ) : ℝ) ∧
    logKernel ((2183 / 64 : ℚ) : ℝ) ≤ ((51080237763149 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2183
  constructor
  · exact (show ((6385029720393 / 9007199254740992 : ℚ) : ℝ) ≤ zKernel ((21363734703373177 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2183 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((42727469406746357 / 18446744073709551616 : ℚ) : ℝ) ≤ ((51080237763149 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2184 : ((42065041393199377 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((273 / 8 : ℚ) : ℝ) ∧
    heightZ ((273 / 8 : ℚ) : ℝ) ≤ ((10516260348299845 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((42065041393199377 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((273 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-103 / 24 : ℚ) : ℝ) ∧
      Real.exp (-((273 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-103 / 24 : ℚ) : ℝ) ≤ ((10516260348299845 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2184 : ((49508664064993 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((273 / 8 : ℚ) : ℝ) ∧
    logKernel ((273 / 8 : ℚ) : ℝ) ≤ ((24754332032499 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2184
  constructor
  · exact (show ((49508664064993 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((42065041393199377 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((273 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((10516260348299845 / 4611686018427387904 : ℚ) : ℝ) ≤ ((24754332032499 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2185 : ((41412883374089807 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2185 / 64 : ℚ) : ℝ) ∧
    heightZ ((2185 / 64 : ℚ) : ℝ) ≤ ((20706441687044905 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((41412883374089807 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2185 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-827 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2185 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-827 / 192 : ℚ) : ℝ) ≤ ((20706441687044905 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2185 : ((11996360651579 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((2185 / 64 : ℚ) : ℝ) ∧
    logKernel ((2185 / 64 : ℚ) : ℝ) ≤ ((47985442606321 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2185
  constructor
  · exact (show ((11996360651579 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((41412883374089807 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2185 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((20706441687044905 / 9223372036854775808 : ℚ) : ℝ) ≤ ((47985442606321 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2186 : ((40770836127911931 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1093 / 32 : ℚ) : ℝ) ∧
    heightZ ((1093 / 32 : ℚ) : ℝ) ≤ ((20385418063955967 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((40770836127911931 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1093 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-415 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1093 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-415 / 96 : ℚ) : ℝ) ≤ ((20385418063955967 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2186 : ((23254542872549 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((1093 / 32 : ℚ) : ℝ) ∧
    logKernel ((1093 / 32 : ℚ) : ℝ) ≤ ((46509085745103 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2186
  constructor
  · exact (show ((23254542872549 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((40770836127911931 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1093 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((20385418063955967 / 9223372036854775808 : ℚ) : ℝ) ≤ ((46509085745103 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2187 : ((20069371450830339 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2187 / 64 : ℚ) : ℝ) ∧
    heightZ ((2187 / 64 : ℚ) : ℝ) ≤ ((40138742901660681 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((20069371450830339 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2187 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-833 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2187 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-833 / 192 : ℚ) : ℝ) ≤ ((40138742901660681 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2187 : ((45078151609259 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2187 / 64 : ℚ) : ℝ) ∧
    logKernel ((2187 / 64 : ℚ) : ℝ) ≤ ((2817384475579 / 4503599627370496 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2187
  constructor
  · exact (show ((45078151609259 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((20069371450830339 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2187 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((40138742901660681 / 18446744073709551616 : ℚ) : ℝ) ≤ ((2817384475579 / 4503599627370496 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2188 : ((39516449372561065 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((547 / 16 : ℚ) : ℝ) ∧
    heightZ ((547 / 16 : ℚ) : ℝ) ≤ ((9879112343140267 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((39516449372561065 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((547 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-209 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((547 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-209 / 48 : ℚ) : ℝ) ≤ ((9879112343140267 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2188 : ((43691242688457 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((547 / 16 : ℚ) : ℝ) ∧
    logKernel ((547 / 16 : ℚ) : ℝ) ≤ ((21845621344231 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2188
  constructor
  · exact (show ((43691242688457 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((39516449372561065 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((547 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((9879112343140267 / 4611686018427387904 : ℚ) : ℝ) ≤ ((21845621344231 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2189 : ((38903803610390975 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2189 / 64 : ℚ) : ℝ) ∧
    heightZ ((2189 / 64 : ℚ) : ℝ) ≤ ((19451901805195489 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((38903803610390975 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2189 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-839 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2189 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-839 / 192 : ℚ) : ℝ) ≤ ((19451901805195489 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2189 : ((5293375558653 / 9007199254740992 : ℚ) : ℝ) ≤ logKernel ((2189 / 64 : ℚ) : ℝ) ∧
    logKernel ((2189 / 64 : ℚ) : ℝ) ≤ ((42347004469229 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2189
  constructor
  · exact (show ((5293375558653 / 9007199254740992 : ℚ) : ℝ) ≤ zKernel ((38903803610390975 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2189 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((19451901805195489 / 9223372036854775808 : ℚ) : ℝ) ≤ ((42347004469229 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2190 : ((38300656040388059 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1095 / 32 : ℚ) : ℝ) ∧
    heightZ ((1095 / 32 : ℚ) : ℝ) ≤ ((19150328020194031 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((38300656040388059 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1095 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-421 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1095 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-421 / 96 : ℚ) : ℝ) ≤ ((19150328020194031 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2190 : ((20522062056045 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((1095 / 32 : ℚ) : ℝ) ∧
    logKernel ((1095 / 32 : ℚ) : ℝ) ≤ ((41044124112095 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2190
  constructor
  · exact (show ((20522062056045 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((38300656040388059 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1095 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((19150328020194031 / 9223372036854775808 : ℚ) : ℝ) ≤ ((41044124112095 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2191 : ((37706859406731717 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2191 / 64 : ℚ) : ℝ) ∧
    heightZ ((2191 / 64 : ℚ) : ℝ) ≤ ((4713357425841465 / 2305843009213693952 : ℚ) : ℝ) := by
  have h : ((37706859406731717 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2191 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-845 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2191 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-845 / 192 : ℚ) : ℝ) ≤ ((4713357425841465 / 2305843009213693952 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2191 : ((19890664584705 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2191 / 64 : ℚ) : ℝ) ∧
    logKernel ((2191 / 64 : ℚ) : ℝ) ≤ ((39781329169415 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2191
  constructor
  · exact (show ((19890664584705 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((37706859406731717 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2191 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((4713357425841465 / 2305843009213693952 : ℚ) : ℝ) ≤ ((39781329169415 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2192 : ((9280567184147811 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((137 / 4 : ℚ) : ℝ) ∧
    heightZ ((137 / 4 : ℚ) : ℝ) ≤ ((37122268736591247 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((9280567184147811 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((137 / 4 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-53 / 12 : ℚ) : ℝ) ∧
      Real.exp (-((137 / 4 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-53 / 12 : ℚ) : ℝ) ≤ ((37122268736591247 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2192 : ((38557386342635 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((137 / 4 : ℚ) : ℝ) ∧
    logKernel ((137 / 4 : ℚ) : ℝ) ≤ ((2409836646415 / 4503599627370496 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2192
  constructor
  · exact (show ((38557386342635 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((9280567184147811 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((137 / 4 : ℚ) : ℝ)) hh).trans
      (show zKernel ((37122268736591247 / 18446744073709551616 : ℚ) : ℝ) ≤ ((2409836646415 / 4503599627370496 : ℚ) : ℝ) by norm_num [zKernel])

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

theorem log_height_bounds_320 : ((126817975731602357 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((1081 / 32 : ℚ) : ℝ) ∧
    Real.log ((1081 / 32 : ℚ) : ℝ) ≤ ((253635951463204717 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((126817975731602357 / 36028797018963968 : ℚ) : ℝ) ≤ ((1081 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1081 / 32 : ℚ) : ℝ) ≤ Real.exp ((253635951463204717 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_320 : heightPower (320 : Fin 988) ≤ ((1452560319069065 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_320
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_320 : heightFactor (320 : Fin 988) ≤ ((155638500030621 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_320
  obtain ⟨hpl, hph⟩ := kernel_bounds_2161
  obtain ⟨hcl, hch⟩ := kernel_bounds_2162
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2162
  have h : (((1168561 / 512 : ℚ) : ℝ) * (logKernel ((2161 / 64 : ℚ) : ℝ) - logKernel ((1081 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1081 / 32 : ℚ) : ℝ) + Real.log ((1081 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((155638500030621 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_321 : ((253669272894567485 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2163 / 64 : ℚ) : ℝ) ∧
    Real.log ((2163 / 64 : ℚ) : ℝ) ≤ ((3963582388977617 / 1125899906842624 : ℚ) : ℝ) := by
  have hl : Real.exp ((253669272894567485 / 72057594037927936 : ℚ) : ℝ) ≤ ((2163 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2163 / 64 : ℚ) : ℝ) ≤ Real.exp ((3963582388977617 / 1125899906842624 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_321 : heightPower (321 : Fin 988) ≤ ((728544263710715 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_321
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_321 : heightFactor (321 : Fin 988) ≤ ((151801438633065 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_321
  obtain ⟨hpl, hph⟩ := kernel_bounds_2162
  obtain ⟨hcl, hch⟩ := kernel_bounds_2163
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2163
  have h : (((4678569 / 2048 : ℚ) : ℝ) * (logKernel ((1081 / 32 : ℚ) : ℝ) - logKernel ((2163 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2163 / 64 : ℚ) : ℝ) + Real.log ((2163 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((151801438633065 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_322 : ((253702578924297461 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((541 / 16 : ℚ) : ℝ) ∧
    Real.log ((541 / 16 : ℚ) : ℝ) ≤ ((31712822365537183 / 9007199254740992 : ℚ) : ℝ) := by
  have hl : Real.exp ((253702578924297461 / 72057594037927936 : ℚ) : ℝ) ≤ ((541 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((541 / 16 : ℚ) : ℝ) ≤ Real.exp ((31712822365537183 / 9007199254740992 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_322 : heightPower (322 : Fin 988) ≤ ((730808337805583 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_322
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_322 : heightFactor (322 : Fin 988) ≤ ((37014725267231 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_322
  obtain ⟨hpl, hph⟩ := kernel_bounds_2163
  obtain ⟨hcl, hch⟩ := kernel_bounds_2164
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2164
  have h : (((292681 / 128 : ℚ) : ℝ) * (logKernel ((2163 / 64 : ℚ) : ℝ) - logKernel ((541 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((541 / 16 : ℚ) : ℝ) + Real.log ((541 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((37014725267231 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_323 : ((31716983695828221 / 9007199254740992 : ℚ) : ℝ) ≤ Real.log ((2165 / 64 : ℚ) : ℝ) ∧
    Real.log ((2165 / 64 : ℚ) : ℝ) ≤ ((253735869566625771 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((31716983695828221 / 9007199254740992 : ℚ) : ℝ) ≤ ((2165 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2165 / 64 : ℚ) : ℝ) ≤ Real.exp ((253735869566625771 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_323 : heightPower (323 : Fin 988) ≤ ((1466144763693865 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_323
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_323 : heightFactor (323 : Fin 988) ≤ ((72204280342825 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_323
  obtain ⟨hpl, hph⟩ := kernel_bounds_2164
  obtain ⟨hcl, hch⟩ := kernel_bounds_2165
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2165
  have h : (((4687225 / 2048 : ℚ) : ℝ) * (logKernel ((541 / 16 : ℚ) : ℝ) - logKernel ((2165 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2165 / 64 : ℚ) : ℝ) + Real.log ((2165 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((72204280342825 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_324 : ((63442286208940953 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((1083 / 32 : ℚ) : ℝ) ∧
    Real.log ((1083 / 32 : ℚ) : ℝ) ≤ ((253769144835763815 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((63442286208940953 / 18014398509481984 : ℚ) : ℝ) ≤ ((1083 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1083 / 32 : ℚ) : ℝ) ≤ Real.exp ((253769144835763815 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_324 : heightPower (324 : Fin 988) ≤ ((91917049482815 / 17592186044416 : ℚ) : ℝ) := by
  have hh := log_height_bounds_324
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_324 : heightFactor (324 : Fin 988) ≤ ((70424074025841 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_324
  obtain ⟨hpl, hph⟩ := kernel_bounds_2165
  obtain ⟨hcl, hch⟩ := kernel_bounds_2166
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2166
  have h : (((1172889 / 512 : ℚ) : ℝ) * (logKernel ((2165 / 64 : ℚ) : ℝ) - logKernel ((1083 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1083 / 32 : ℚ) : ℝ) + Real.log ((1083 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((70424074025841 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_325 : ((253802404745903325 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2167 / 64 : ℚ) : ℝ) ∧
    Real.log ((2167 / 64 : ℚ) : ℝ) ≤ ((7931325148309479 / 2251799813685248 : ℚ) : ℝ) := by
  have hl : Real.exp ((253802404745903325 / 72057594037927936 : ℚ) : ℝ) ≤ ((2167 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2167 / 64 : ℚ) : ℝ) ≤ Real.exp ((7931325148309479 / 2251799813685248 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_325 : heightPower (325 : Fin 988) ≤ ((737600379880063 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_325
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_325 : heightFactor (325 : Fin 988) ≤ ((2146491399225 / 4398046511104 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_325
  obtain ⟨hpl, hph⟩ := kernel_bounds_2166
  obtain ⟨hcl, hch⟩ := kernel_bounds_2167
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2167
  have h : (((4695889 / 2048 : ℚ) : ℝ) * (logKernel ((1083 / 32 : ℚ) : ℝ) - logKernel ((2167 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2167 / 64 : ℚ) : ℝ) + Real.log ((2167 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((2146491399225 / 4398046511104 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_326 : ((31729456163902049 / 9007199254740992 : ℚ) : ℝ) ≤ Real.log ((271 / 8 : ℚ) : ℝ) ∧
    Real.log ((271 / 8 : ℚ) : ℝ) ≤ ((253835649311216395 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((31729456163902049 / 9007199254740992 : ℚ) : ℝ) ≤ ((271 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((271 / 8 : ℚ) : ℝ) ≤ Real.exp ((253835649311216395 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_326 : heightPower (326 : Fin 988) ≤ ((1479728667854485 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_326
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_326 : heightFactor (326 : Fin 988) ≤ ((133988306008607 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_326
  obtain ⟨hpl, hph⟩ := kernel_bounds_2167
  obtain ⟨hcl, hch⟩ := kernel_bounds_2168
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2168
  have h : (((73441 / 32 : ℚ) : ℝ) * (logKernel ((2167 / 64 : ℚ) : ℝ) - logKernel ((271 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((271 / 8 : ℚ) : ℝ) + Real.log ((271 / 8 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((133988306008607 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_327 : ((253868878545855495 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2169 / 64 : ℚ) : ℝ) ∧
    Real.log ((2169 / 64 : ℚ) : ℝ) ≤ ((126934439272927749 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((253868878545855495 / 72057594037927936 : ℚ) : ℝ) ≤ ((2169 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2169 / 64 : ℚ) : ℝ) ≤ Real.exp ((126934439272927749 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_327 : heightPower (327 : Fin 988) ≤ ((742128258031699 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_327
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_327 : heightFactor (327 : Fin 988) ≤ ((65342305679337 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_327
  obtain ⟨hpl, hph⟩ := kernel_bounds_2168
  obtain ⟨hcl, hch⟩ := kernel_bounds_2169
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2169
  have h : (((4704561 / 2048 : ℚ) : ℝ) * (logKernel ((271 / 8 : ℚ) : ℝ) - logKernel ((2169 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2169 / 64 : ℚ) : ℝ) + Real.log ((2169 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((65342305679337 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_328 : ((31737761557994193 / 9007199254740992 : ℚ) : ℝ) ≤ Real.log ((1085 / 32 : ℚ) : ℝ) ∧
    Real.log ((1085 / 32 : ℚ) : ℝ) ≤ ((253902092463953547 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((31737761557994193 / 9007199254740992 : ℚ) : ℝ) ≤ ((1085 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1085 / 32 : ℚ) : ℝ) ≤ Real.exp ((253902092463953547 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_328 : heightPower (328 : Fin 988) ≤ ((186098038055259 / 35184372088832 : ℚ) : ℝ) := by
  have hh := log_height_bounds_328
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_328 : heightFactor (328 : Fin 988) ≤ ((127462311333537 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_328
  obtain ⟨hpl, hph⟩ := kernel_bounds_2169
  obtain ⟨hcl, hch⟩ := kernel_bounds_2170
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2170
  have h : (((1177225 / 512 : ℚ) : ℝ) * (logKernel ((2169 / 64 : ℚ) : ℝ) - logKernel ((1085 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1085 / 32 : ℚ) : ℝ) + Real.log ((1085 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((127462311333537 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_329 : ((63483822769905979 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((2171 / 64 : ℚ) : ℝ) ∧
    Real.log ((2171 / 64 : ℚ) : ℝ) ≤ ((253935291079623919 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((63483822769905979 / 18014398509481984 : ℚ) : ℝ) ≤ ((2171 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2171 / 64 : ℚ) : ℝ) ≤ Real.exp ((253935291079623919 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_329 : heightPower (329 : Fin 988) ≤ ((746656016522819 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_329
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_329 : heightFactor (329 : Fin 988) ≤ ((1942490659277 / 4398046511104 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_329
  obtain ⟨hpl, hph⟩ := kernel_bounds_2170
  obtain ⟨hcl, hch⟩ := kernel_bounds_2171
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2171
  have h : (((4713241 / 2048 : ℚ) : ℝ) * (logKernel ((1085 / 32 : ℚ) : ℝ) - logKernel ((2171 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2171 / 64 : ℚ) : ℝ) + Real.log ((2171 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1942490659277 / 4398046511104 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_330 : ((126984237203480245 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((543 / 16 : ℚ) : ℝ) ∧
    Real.log ((543 / 16 : ℚ) : ℝ) ≤ ((253968474406960493 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((126984237203480245 / 36028797018963968 : ℚ) : ℝ) ≤ ((543 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((543 / 16 : ℚ) : ℝ) ≤ Real.exp ((253968474406960493 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_330 : heightPower (330 : Fin 988) ≤ ((1497839701929151 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_330
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_330 : heightFactor (330 : Fin 988) ≤ ((30313482371417 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_330
  obtain ⟨hpl, hph⟩ := kernel_bounds_2171
  obtain ⟨hcl, hch⟩ := kernel_bounds_2172
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2172
  have h : (((294849 / 128 : ℚ) : ℝ) * (logKernel ((2171 / 64 : ℚ) : ℝ) - logKernel ((543 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((543 / 16 : ℚ) : ℝ) + Real.log ((543 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((30313482371417 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_331 : ((15875102653752355 / 4503599627370496 : ℚ) : ℝ) ≤ Real.log ((2173 / 64 : ℚ) : ℝ) ∧
    Real.log ((2173 / 64 : ℚ) : ℝ) ≤ ((254001642460037683 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((15875102653752355 / 4503599627370496 : ℚ) : ℝ) ≤ ((2173 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2173 / 64 : ℚ) : ℝ) ≤ Real.exp ((254001642460037683 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_331 : heightPower (331 : Fin 988) ≤ ((375591827786897 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_331
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_331 : heightFactor (331 : Fin 988) ≤ ((3695749588451 / 8796093022208 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_331
  obtain ⟨hpl, hph⟩ := kernel_bounds_2172
  obtain ⟨hcl, hch⟩ := kernel_bounds_2173
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2173
  have h : (((4721929 / 2048 : ℚ) : ℝ) * (logKernel ((543 / 16 : ℚ) : ℝ) - logKernel ((2173 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2173 / 64 : ℚ) : ℝ) + Real.log ((2173 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((3695749588451 / 8796093022208 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_332 : ((254034795252910479 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1087 / 32 : ℚ) : ℝ) ∧
    Real.log ((1087 / 32 : ℚ) : ℝ) ≤ ((127017397626455241 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((254034795252910479 / 72057594037927936 : ℚ) : ℝ) ≤ ((1087 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1087 / 32 : ℚ) : ℝ) ≤ Real.exp ((127017397626455241 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_332 : heightPower (332 : Fin 988) ≤ ((1506894860755851 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_332
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_332 : heightFactor (332 : Fin 988) ≤ ((28836928685569 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_332
  obtain ⟨hpl, hph⟩ := kernel_bounds_2173
  obtain ⟨hcl, hch⟩ := kernel_bounds_2174
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2174
  have h : (((1181569 / 512 : ℚ) : ℝ) * (logKernel ((2173 / 64 : ℚ) : ℝ) - logKernel ((1087 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1087 / 32 : ℚ) : ℝ) + Real.log ((1087 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((28836928685569 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_333 : ((254067932799614483 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2175 / 64 : ℚ) : ℝ) ∧
    Real.log ((2175 / 64 : ℚ) : ℝ) ≤ ((127033966399807243 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((254067932799614483 / 72057594037927936 : ℚ) : ℝ) ≤ ((2175 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2175 / 64 : ℚ) : ℝ) ≤ Real.exp ((127033966399807243 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_333 : heightPower (333 : Fin 988) ≤ ((23615974231387 / 4398046511104 : ℚ) : ℝ) := by
  have hh := log_height_bounds_333
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_333 : heightFactor (333 : Fin 988) ≤ ((56251649738075 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_333
  obtain ⟨hpl, hph⟩ := kernel_bounds_2174
  obtain ⟨hcl, hch⟩ := kernel_bounds_2175
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2175
  have h : (((4730625 / 2048 : ℚ) : ℝ) * (logKernel ((1087 / 32 : ℚ) : ℝ) - logKernel ((2175 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2175 / 64 : ℚ) : ℝ) + Real.log ((2175 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((56251649738075 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_334 : ((127050527557082969 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((34 / 1 : ℚ) : ℝ) ∧
    Real.log ((34 / 1 : ℚ) : ℝ) ≤ ((254101055114165941 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((127050527557082969 / 36028797018963968 : ℚ) : ℝ) ≤ ((34 / 1 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((34 / 1 : ℚ) : ℝ) ≤ Real.exp ((254101055114165941 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_334 : heightPower (334 : Fin 988) ≤ ((23686715333767 / 4398046511104 : ℚ) : ℝ) := by
  have hh := log_height_bounds_334
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_334 : heightFactor (334 : Fin 988) ≤ ((109728971903527 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_334
  obtain ⟨hpl, hph⟩ := kernel_bounds_2175
  obtain ⟨hcl, hch⟩ := kernel_bounds_2176
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2176
  have h : (((2312 / 1 : ℚ) : ℝ) * (logKernel ((2175 / 64 : ℚ) : ℝ) - logKernel ((34 / 1 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((34 / 1 : ℚ) : ℝ) + Real.log ((34 / 1 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((109728971903527 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_335 : ((31766770276320221 / 9007199254740992 : ℚ) : ℝ) ≤ Real.log ((2177 / 64 : ℚ) : ℝ) ∧
    Real.log ((2177 / 64 : ℚ) : ℝ) ≤ ((254134162210561771 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((31766770276320221 / 9007199254740992 : ℚ) : ℝ) ≤ ((2177 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2177 / 64 : ℚ) : ℝ) ≤ Real.exp ((254134162210561771 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_335 : heightPower (335 : Fin 988) ≤ ((47514911014609 / 8796093022208 : ℚ) : ℝ) := by
  have hh := log_height_bounds_335
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_335 : heightFactor (335 : Fin 988) ≤ ((53511503207913 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_335
  obtain ⟨hpl, hph⟩ := kernel_bounds_2176
  obtain ⟨hcl, hch⟩ := kernel_bounds_2177
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2177
  have h : (((4739329 / 2048 : ℚ) : ℝ) * (logKernel ((34 / 1 : ℚ) : ℝ) - logKernel ((2177 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2177 / 64 : ℚ) : ℝ) + Real.log ((2177 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((53511503207913 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_336 : ((254167254102779615 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1089 / 32 : ℚ) : ℝ) ∧
    Real.log ((1089 / 32 : ℚ) : ℝ) ≤ ((127083627051389809 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((254167254102779615 / 72057594037927936 : ℚ) : ℝ) ≤ ((1089 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1089 / 32 : ℚ) : ℝ) ≤ Real.exp ((127083627051389809 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_336 : heightPower (336 : Fin 988) ≤ ((190625558022821 / 35184372088832 : ℚ) : ℝ) := by
  have hh := log_height_bounds_336
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_336 : heightFactor (336 : Fin 988) ≤ ((104383719854771 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_336
  obtain ⟨hpl, hph⟩ := kernel_bounds_2177
  obtain ⟨hcl, hch⟩ := kernel_bounds_2178
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2178
  have h : (((1185921 / 512 : ℚ) : ℝ) * (logKernel ((2177 / 64 : ℚ) : ℝ) - logKernel ((1089 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1089 / 32 : ℚ) : ℝ) + Real.log ((1089 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((104383719854771 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_337 : ((127100165402388935 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2179 / 64 : ℚ) : ℝ) ∧
    Real.log ((2179 / 64 : ℚ) : ℝ) ≤ ((254200330804777873 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((127100165402388935 / 36028797018963968 : ℚ) : ℝ) ≤ ((2179 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2179 / 64 : ℚ) : ℝ) ≤ Real.exp ((254200330804777873 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_337 : heightPower (337 : Fin 988) ≤ ((1529531716560853 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_337
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_337 : heightFactor (337 : Fin 988) ≤ ((50904735234501 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_337
  obtain ⟨hpl, hph⟩ := kernel_bounds_2178
  obtain ⟨hcl, hch⟩ := kernel_bounds_2179
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2179
  have h : (((4748041 / 2048 : ℚ) : ℝ) * (logKernel ((1089 / 32 : ℚ) : ℝ) - logKernel ((2179 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2179 / 64 : ℚ) : ℝ) + Real.log ((2179 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((50904735234501 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_338 : ((7944793510327991 / 2251799813685248 : ℚ) : ℝ) ≤ Real.log ((545 / 16 : ℚ) : ℝ) ∧
    Real.log ((545 / 16 : ℚ) : ℝ) ≤ ((254233392330495715 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((7944793510327991 / 2251799813685248 : ℚ) : ℝ) ≤ ((545 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((545 / 16 : ℚ) : ℝ) ≤ Real.exp ((254233392330495715 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_338 : heightPower (338 : Fin 988) ≤ ((191757363707099 / 35184372088832 : ℚ) : ℝ) := by
  have hh := log_height_bounds_338
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_338 : heightFactor (338 : Fin 988) ≤ ((99298656896327 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_338
  obtain ⟨hpl, hph⟩ := kernel_bounds_2179
  obtain ⟨hcl, hch⟩ := kernel_bounds_2180
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2180
  have h : (((297025 / 128 : ℚ) : ℝ) * (logKernel ((2179 / 64 : ℚ) : ℝ) - logKernel ((545 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((545 / 16 : ℚ) : ℝ) + Real.log ((545 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((99298656896327 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_339 : ((31783304836731643 / 9007199254740992 : ℚ) : ℝ) ≤ Real.log ((2181 / 64 : ℚ) : ℝ) ∧
    Real.log ((2181 / 64 : ℚ) : ℝ) ≤ ((254266438693853147 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((31783304836731643 / 9007199254740992 : ℚ) : ℝ) ≤ ((2181 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2181 / 64 : ℚ) : ℝ) ≤ Real.exp ((254266438693853147 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_339 : heightPower (339 : Fin 988) ≤ ((1538586043524761 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_339
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_339 : heightFactor (339 : Fin 988) ≤ ((96849717170947 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_339
  obtain ⟨hpl, hph⟩ := kernel_bounds_2180
  obtain ⟨hcl, hch⟩ := kernel_bounds_2181
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2181
  have h : (((4756761 / 2048 : ℚ) : ℝ) * (logKernel ((545 / 16 : ℚ) : ℝ) - logKernel ((2181 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2181 / 64 : ℚ) : ℝ) + Real.log ((2181 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((96849717170947 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_340 : ((127149734954375511 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((1091 / 32 : ℚ) : ℝ) ∧
    Real.log ((1091 / 32 : ℚ) : ℝ) ≤ ((254299469908751025 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((127149734954375511 / 36028797018963968 : ℚ) : ℝ) ≤ ((1091 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1091 / 32 : ℚ) : ℝ) ≤ Real.exp ((254299469908751025 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_340 : heightPower (340 : Fin 988) ≤ ((385778279554765 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_340
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_340 : heightFactor (340 : Fin 988) ≤ ((11807640969385 / 35184372088832 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_340
  obtain ⟨hpl, hph⟩ := kernel_bounds_2181
  obtain ⟨hcl, hch⟩ := kernel_bounds_2182
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2182
  have h : (((1190281 / 512 : ℚ) : ℝ) * (logKernel ((2181 / 64 : ℚ) : ℝ) - logKernel ((1091 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1091 / 32 : ℚ) : ℝ) + Real.log ((1091 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((11807640969385 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_341 : ((254332485989071097 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2183 / 64 : ℚ) : ℝ) ∧
    Real.log ((2183 / 64 : ℚ) : ℝ) ≤ ((63583121497267775 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((254332485989071097 / 72057594037927936 : ℚ) : ℝ) ≤ ((2183 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2183 / 64 : ℚ) : ℝ) ≤ Real.exp ((63583121497267775 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_341 : heightPower (341 : Fin 988) ≤ ((773820066896957 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_341
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_341 : heightFactor (341 : Fin 988) ≤ ((92131402594353 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_341
  obtain ⟨hpl, hph⟩ := kernel_bounds_2182
  obtain ⟨hcl, hch⟩ := kernel_bounds_2183
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2183
  have h : (((4765489 / 2048 : ℚ) : ℝ) * (logKernel ((1091 / 32 : ℚ) : ℝ) - logKernel ((2183 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2183 / 64 : ℚ) : ℝ) + Real.log ((2183 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((92131402594353 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_342 : ((15897842934292253 / 4503599627370496 : ℚ) : ℝ) ≤ Real.log ((273 / 8 : ℚ) : ℝ) ∧
    Real.log ((273 / 8 : ℚ) : ℝ) ≤ ((254365486948676051 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((15897842934292253 / 4503599627370496 : ℚ) : ℝ) ≤ ((273 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((273 / 8 : ℚ) : ℝ) ≤ Real.exp ((254365486948676051 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_342 : heightPower (342 : Fin 988) ≤ ((1552167090303475 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_342
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_342 : heightFactor (342 : Fin 988) ≤ ((5616193262275 / 17592186044416 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_342
  obtain ⟨hpl, hph⟩ := kernel_bounds_2183
  obtain ⟨hcl, hch⟩ := kernel_bounds_2184
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2184
  have h : (((74529 / 32 : ℚ) : ℝ) * (logKernel ((2183 / 64 : ℚ) : ℝ) - logKernel ((273 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((273 / 8 : ℚ) : ℝ) + Real.log ((273 / 8 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((5616193262275 / 17592186044416 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_343 : ((254398472801409515 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2185 / 64 : ℚ) : ℝ) ∧
    Real.log ((2185 / 64 : ℚ) : ℝ) ≤ ((127199236400704759 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((254398472801409515 / 72057594037927936 : ℚ) : ℝ) ≤ ((2185 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2185 / 64 : ℚ) : ℝ) ≤ Real.exp ((127199236400704759 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_343 : heightPower (343 : Fin 988) ≤ ((1556693987801819 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_343
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_343 : heightFactor (343 : Fin 988) ≤ ((43821391366043 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_343
  obtain ⟨hpl, hph⟩ := kernel_bounds_2184
  obtain ⟨hcl, hch⟩ := kernel_bounds_2185
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2185
  have h : (((4774225 / 2048 : ℚ) : ℝ) * (logKernel ((273 / 8 : ℚ) : ℝ) - logKernel ((2185 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2185 / 64 : ℚ) : ℝ) + Real.log ((2185 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((43821391366043 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_344 : ((127215721780548067 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((1093 / 32 : ℚ) : ℝ) ∧
    Real.log ((1093 / 32 : ℚ) : ℝ) ≤ ((254431443561096137 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((127215721780548067 / 36028797018963968 : ℚ) : ℝ) ≤ ((1093 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1093 / 32 : ℚ) : ℝ) ≤ Real.exp ((254431443561096137 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_344 : heightPower (344 : Fin 988) ≤ ((1561220826342949 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_344
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_344 : heightFactor (344 : Fin 988) ≤ ((42740547579403 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_344
  obtain ⟨hpl, hph⟩ := kernel_bounds_2185
  obtain ⟨hcl, hch⟩ := kernel_bounds_2186
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2186
  have h : (((1194649 / 512 : ℚ) : ℝ) * (logKernel ((2185 / 64 : ℚ) : ℝ) - logKernel ((1093 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1093 / 32 : ℚ) : ℝ) + Real.log ((1093 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((42740547579403 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_345 : ((254464399241541575 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2187 / 64 : ℚ) : ℝ) ∧
    Real.log ((2187 / 64 : ℚ) : ℝ) ≤ ((127232199620770789 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((254464399241541575 / 72057594037927936 : ℚ) : ℝ) ≤ ((2187 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2187 / 64 : ℚ) : ℝ) ≤ Real.exp ((127232199620770789 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_345 : heightPower (345 : Fin 988) ≤ ((1565747605980793 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_345
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_345 : heightFactor (345 : Fin 988) ≤ ((83372684365319 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_345
  obtain ⟨hpl, hph⟩ := kernel_bounds_2186
  obtain ⟨hcl, hch⟩ := kernel_bounds_2187
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2187
  have h : (((4782969 / 2048 : ℚ) : ℝ) * (logKernel ((1093 / 32 : ℚ) : ℝ) - logKernel ((2187 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2187 / 64 : ℚ) : ℝ) + Real.log ((2187 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((83372684365319 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_346 : ((254497339856532573 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((547 / 16 : ℚ) : ℝ) ∧
    Real.log ((547 / 16 : ℚ) : ℝ) ≤ ((7953041870516643 / 2251799813685248 : ℚ) : ℝ) := by
  have hl : Real.exp ((254497339856532573 / 72057594037927936 : ℚ) : ℝ) ≤ ((547 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((547 / 16 : ℚ) : ℝ) ≤ Real.exp ((7953041870516643 / 2251799813685248 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_346 : heightPower (346 : Fin 988) ≤ ((785137163384603 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_346
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_346 : heightFactor (346 : Fin 988) ≤ ((20329059584395 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_346
  obtain ⟨hpl, hph⟩ := kernel_bounds_2187
  obtain ⟨hcl, hch⟩ := kernel_bounds_2188
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2188
  have h : (((299209 / 128 : ℚ) : ℝ) * (logKernel ((2187 / 64 : ℚ) : ℝ) - logKernel ((547 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((547 / 16 : ℚ) : ℝ) + Real.log ((547 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((20329059584395 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_347 : ((254530265419836965 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2189 / 64 : ℚ) : ℝ) ∧
    Real.log ((2189 / 64 : ℚ) : ℝ) ≤ ((31816283177479621 / 9007199254740992 : ℚ) : ℝ) := by
  have hl : Real.exp ((254530265419836965 / 72057594037927936 : ℚ) : ℝ) ≤ ((2189 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2189 / 64 : ℚ) : ℝ) ≤ Real.exp ((31816283177479621 / 9007199254740992 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_347 : heightPower (347 : Fin 988) ≤ ((98425061797623 / 17592186044416 : ℚ) : ℝ) := by
  have hh := log_height_bounds_347
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_347 : heightFactor (347 : Fin 988) ≤ ((79310477345065 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_347
  obtain ⟨hpl, hph⟩ := kernel_bounds_2188
  obtain ⟨hcl, hch⟩ := kernel_bounds_2189
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2189
  have h : (((4791721 / 2048 : ℚ) : ℝ) * (logKernel ((547 / 16 : ℚ) : ℝ) - logKernel ((2189 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2189 / 64 : ℚ) : ℝ) + Real.log ((2189 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((79310477345065 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_348 : ((254563175945203723 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1095 / 32 : ℚ) : ℝ) ∧
    Real.log ((1095 / 32 : ℚ) : ℝ) ≤ ((127281587972601863 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((254563175945203723 / 72057594037927936 : ℚ) : ℝ) ≤ ((1095 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1095 / 32 : ℚ) : ℝ) ≤ Real.exp ((127281587972601863 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_348 : heightPower (348 : Fin 988) ≤ ((789663796006393 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_348
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_348 : heightFactor (348 : Fin 988) ≤ ((38677076573543 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_348
  obtain ⟨hpl, hph⟩ := kernel_bounds_2189
  obtain ⟨hcl, hch⟩ := kernel_bounds_2190
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2190
  have h : (((1199025 / 512 : ℚ) : ℝ) * (logKernel ((2189 / 64 : ℚ) : ℝ) - logKernel ((1095 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1095 / 32 : ℚ) : ℝ) + Real.log ((1095 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((38677076573543 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_349 : ((127298035723181495 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2191 / 64 : ℚ) : ℝ) ∧
    Real.log ((2191 / 64 : ℚ) : ℝ) ≤ ((254596071446362993 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((127298035723181495 / 36028797018963968 : ℚ) : ℝ) ≤ ((2191 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2191 / 64 : ℚ) : ℝ) ≤ Real.exp ((254596071446362993 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_349 : heightPower (349 : Fin 988) ≤ ((1583854136575293 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_349
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_349 : heightFactor (349 : Fin 988) ≤ ((75446048218589 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_349
  obtain ⟨hpl, hph⟩ := kernel_bounds_2190
  obtain ⟨hcl, hch⟩ := kernel_bounds_2191
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2191
  have h : (((4800481 / 2048 : ℚ) : ℝ) * (logKernel ((1095 / 32 : ℚ) : ℝ) - logKernel ((2191 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2191 / 64 : ℚ) : ℝ) + Real.log ((2191 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((75446048218589 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_350 : ((3978577374016033 / 1125899906842624 : ℚ) : ℝ) ≤ Real.log ((137 / 4 : ℚ) : ℝ) ∧
    Real.log ((137 / 4 : ℚ) : ℝ) ≤ ((254628951937026115 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((3978577374016033 / 1125899906842624 : ℚ) : ℝ) ≤ ((137 / 4 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((137 / 4 : ℚ) : ℝ) ≤ Real.exp ((254628951937026115 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_350 : heightPower (350 : Fin 988) ≤ ((794190311251525 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_350
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_350 : heightFactor (350 : Fin 988) ≤ ((36792487497491 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_350
  obtain ⟨hpl, hph⟩ := kernel_bounds_2191
  obtain ⟨hcl, hch⟩ := kernel_bounds_2192
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2192
  have h : (((18769 / 8 : ℚ) : ℝ) * (logKernel ((2191 / 64 : ℚ) : ℝ) - logKernel ((137 / 4 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((137 / 4 : ℚ) : ℝ) + Real.log ((137 / 4 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((36792487497491 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_351 : ((254661817430885675 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2193 / 64 : ℚ) : ℝ) ∧
    Real.log ((2193 / 64 : ℚ) : ℝ) ≤ ((127330908715442839 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((254661817430885675 / 72057594037927936 : ℚ) : ℝ) ≤ ((2193 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2193 / 64 : ℚ) : ℝ) ≤ Real.exp ((127330908715442839 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_351 : heightPower (351 : Fin 988) ≤ ((1592907049849543 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_351
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_351 : heightFactor (351 : Fin 988) ≤ ((71769775135505 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_351
  obtain ⟨hpl, hph⟩ := kernel_bounds_2192
  obtain ⟨hcl, hch⟩ := kernel_bounds_2193
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2193
  have h : (((4809249 / 2048 : ℚ) : ℝ) * (logKernel ((137 / 4 : ℚ) : ℝ) - logKernel ((2193 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2193 / 64 : ℚ) : ℝ) + Real.log ((2193 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((71769775135505 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

end LegendreK6.M2Pilot.Enclosures.Height010
