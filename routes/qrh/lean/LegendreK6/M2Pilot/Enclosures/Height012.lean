import LegendreK6.M2PilotDefinitions
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp

/-! Generated proposals: every bound is checked by Lean, not by trusting Arb. -/
namespace LegendreK6.M2Pilot.Enclosures.Height012
set_option maxRecDepth 100000
set_option maxHeartbeats 0

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

theorem height_z_bounds_2226 : ((5455763996934949 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((1113 / 32 : ℚ) : ℝ) ∧
    heightZ ((1113 / 32 : ℚ) : ℝ) ≤ ((21823055987739799 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((5455763996934949 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((1113 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-475 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1113 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-475 / 96 : ℚ) : ℝ) ≤ ((21823055987739799 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2226 : ((13325076163551 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1113 / 32 : ℚ) : ℝ) ∧
    logKernel ((1113 / 32 : ℚ) : ℝ) ≤ ((3331269040889 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2226
  constructor
  · exact (show ((13325076163551 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((5455763996934949 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1113 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((21823055987739799 / 18446744073709551616 : ℚ) : ℝ) ≤ ((3331269040889 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2227 : ((21484720864499373 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2227 / 64 : ℚ) : ℝ) ∧
    heightZ ((2227 / 64 : ℚ) : ℝ) ≤ ((1342795054031211 / 1152921504606846976 : ℚ) : ℝ) := by
  have h : ((21484720864499373 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2227 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-953 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2227 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-953 / 192 : ℚ) : ℝ) ≤ ((1342795054031211 / 1152921504606846976 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2227 : ((6457553334821 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2227 / 64 : ℚ) : ℝ) ∧
    logKernel ((2227 / 64 : ℚ) : ℝ) ≤ ((12915106669647 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2227
  constructor
  · exact (show ((6457553334821 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((21484720864499373 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2227 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1342795054031211 / 1152921504606846976 : ℚ) : ℝ) ≤ ((12915106669647 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2228 : ((21151631141155391 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((557 / 16 : ℚ) : ℝ) ∧
    heightZ ((557 / 16 : ℚ) : ℝ) ≤ ((10575815570577697 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((21151631141155391 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((557 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-239 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((557 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-239 / 48 : ℚ) : ℝ) ≤ ((10575815570577697 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2228 : ((782359413189 / 4503599627370496 : ℚ) : ℝ) ≤ logKernel ((557 / 16 : ℚ) : ℝ) ∧
    logKernel ((557 / 16 : ℚ) : ℝ) ≤ ((12517750611029 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2228
  constructor
  · exact (show ((782359413189 / 4503599627370496 : ℚ) : ℝ) ≤ zKernel ((21151631141155391 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((557 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((10575815570577697 / 9223372036854775808 : ℚ) : ℝ) ≤ ((12517750611029 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2229 : ((20823705495320123 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2229 / 64 : ℚ) : ℝ) ∧
    heightZ ((2229 / 64 : ℚ) : ℝ) ≤ ((10411852747660063 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((20823705495320123 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2229 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-959 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2229 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-959 / 192 : ℚ) : ℝ) ≤ ((10411852747660063 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2229 : ((12132619913091 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2229 / 64 : ℚ) : ℝ) ∧
    logKernel ((2229 / 64 : ℚ) : ℝ) ≤ ((1516577489137 / 9007199254740992 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2229
  constructor
  · exact (show ((12132619913091 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((20823705495320123 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2229 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((10411852747660063 / 9223372036854775808 : ℚ) : ℝ) ≤ ((1516577489137 / 9007199254740992 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2230 : ((5125215966348151 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((1115 / 32 : ℚ) : ℝ) ∧
    heightZ ((1115 / 32 : ℚ) : ℝ) ≤ ((20500863865392607 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((5125215966348151 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((1115 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-481 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1115 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-481 / 96 : ℚ) : ℝ) ≤ ((20500863865392607 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2230 : ((11759338441037 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1115 / 32 : ℚ) : ℝ) ∧
    logKernel ((1115 / 32 : ℚ) : ℝ) ≤ ((5879669220521 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2230
  constructor
  · exact (show ((11759338441037 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((5125215966348151 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1115 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((20500863865392607 / 18446744073709551616 : ℚ) : ℝ) ≤ ((5879669220521 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2231 : ((20183027431011943 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2231 / 64 : ℚ) : ℝ) ∧
    heightZ ((2231 / 64 : ℚ) : ℝ) ≤ ((10091513715505973 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((20183027431011943 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2231 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-965 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2231 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-965 / 192 : ℚ) : ℝ) ≤ ((10091513715505973 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2231 : ((2849385408127 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((2231 / 64 : ℚ) : ℝ) ∧
    logKernel ((2231 / 64 : ℚ) : ℝ) ≤ ((11397541632513 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2231
  constructor
  · exact (show ((2849385408127 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((20183027431011943 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2231 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((10091513715505973 / 9223372036854775808 : ℚ) : ℝ) ≤ ((11397541632513 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2232 : ((19870118593813679 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((279 / 8 : ℚ) : ℝ) ∧
    heightZ ((279 / 8 : ℚ) : ℝ) ≤ ((9935059296906841 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((19870118593813679 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((279 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-121 / 24 : ℚ) : ℝ) ∧
      Real.exp (-((279 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-121 / 24 : ℚ) : ℝ) ≤ ((9935059296906841 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2232 : ((11046876141555 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((279 / 8 : ℚ) : ℝ) ∧
    logKernel ((279 / 8 : ℚ) : ℝ) ≤ ((1380859517695 / 9007199254740992 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2232
  constructor
  · exact (show ((11046876141555 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((19870118593813679 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((279 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((9935059296906841 / 9223372036854775808 : ℚ) : ℝ) ≤ ((1380859517695 / 9007199254740992 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2233 : ((19562060958484483 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2233 / 64 : ℚ) : ℝ) ∧
    heightZ ((2233 / 64 : ℚ) : ℝ) ≤ ((9781030479242243 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((19562060958484483 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2233 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-971 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2233 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-971 / 192 : ℚ) : ℝ) ≤ ((9781030479242243 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2233 : ((10706999493539 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2233 / 64 : ℚ) : ℝ) ∧
    logKernel ((2233 / 64 : ℚ) : ℝ) ≤ ((1338374936693 / 9007199254740992 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2233
  constructor
  · exact (show ((10706999493539 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((19562060958484483 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2233 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((9781030479242243 / 9223372036854775808 : ℚ) : ℝ) ≤ ((1338374936693 / 9007199254740992 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2234 : ((9629389657055289 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((1117 / 32 : ℚ) : ℝ) ∧
    heightZ ((1117 / 32 : ℚ) : ℝ) ≤ ((19258779314110581 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((9629389657055289 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((1117 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-487 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1117 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-487 / 96 : ℚ) : ℝ) ≤ ((19258779314110581 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2234 : ((10377579750659 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1117 / 32 : ℚ) : ℝ) ∧
    logKernel ((1117 / 32 : ℚ) : ℝ) ≤ ((1297197468833 / 9007199254740992 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2234
  constructor
  · exact (show ((10377579750659 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((9629389657055289 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1117 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((19258779314110581 / 18446744073709551616 : ℚ) : ℝ) ≤ ((1297197468833 / 9007199254740992 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2235 : ((18960199615815327 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2235 / 64 : ℚ) : ℝ) ∧
    heightZ ((2235 / 64 : ℚ) : ℝ) ≤ ((9480099807907665 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((18960199615815327 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2235 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-977 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2235 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-977 / 192 : ℚ) : ℝ) ≤ ((9480099807907665 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2235 : ((10058295187767 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2235 / 64 : ℚ) : ℝ) ∧
    logKernel ((2235 / 64 : ℚ) : ℝ) ≤ ((2514573796943 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2235
  constructor
  · exact (show ((10058295187767 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((18960199615815327 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2235 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((9480099807907665 / 9223372036854775808 : ℚ) : ℝ) ≤ ((2514573796943 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2236 : ((18666248966681503 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((559 / 16 : ℚ) : ℝ) ∧
    heightZ ((559 / 16 : ℚ) : ℝ) ≤ ((9333124483340753 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((18666248966681503 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((559 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-245 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((559 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-245 / 48 : ℚ) : ℝ) ≤ ((9333124483340753 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2236 : ((9748833978157 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((559 / 16 : ℚ) : ℝ) ∧
    logKernel ((559 / 16 : ℚ) : ℝ) ≤ ((4874416989081 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2236
  constructor
  · exact (show ((9748833978157 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((18666248966681503 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((559 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((9333124483340753 / 9223372036854775808 : ℚ) : ℝ) ≤ ((4874416989081 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2237 : ((9188427799976913 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2237 / 64 : ℚ) : ℝ) ∧
    heightZ ((2237 / 64 : ℚ) : ℝ) ≤ ((18376855599953829 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((9188427799976913 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2237 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-983 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2237 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-983 / 192 : ℚ) : ℝ) ≤ ((18376855599953829 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2237 : ((4724446944511 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2237 / 64 : ℚ) : ℝ) ∧
    logKernel ((2237 / 64 : ℚ) : ℝ) ≤ ((9448893889027 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2237
  constructor
  · exact (show ((4724446944511 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((9188427799976913 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2237 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((18376855599953829 / 18446744073709551616 : ℚ) : ℝ) ≤ ((9448893889027 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2238 : ((18091948861517429 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1119 / 32 : ℚ) : ℝ) ∧
    heightZ ((1119 / 32 : ℚ) : ℝ) ≤ ((2261493607689679 / 2305843009213693952 : ℚ) : ℝ) := by
  have h : ((18091948861517429 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1119 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-493 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1119 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-493 / 96 : ℚ) : ℝ) ≤ ((2261493607689679 / 2305843009213693952 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2238 : ((9158181986281 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1119 / 32 : ℚ) : ℝ) ∧
    logKernel ((1119 / 32 : ℚ) : ℝ) ≤ ((4579090993143 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2238
  constructor
  · exact (show ((9158181986281 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((18091948861517429 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1119 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((2261493607689679 / 2305843009213693952 : ℚ) : ℝ) ≤ ((4579090993143 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2239 : ((4452864798161991 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((2239 / 64 : ℚ) : ℝ) ∧
    heightZ ((2239 / 64 : ℚ) : ℝ) ≤ ((17811459192647967 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((4452864798161991 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((2239 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-989 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2239 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-989 / 192 : ℚ) : ℝ) ≤ ((17811459192647967 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2239 : ((4438207174243 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2239 / 64 : ℚ) : ℝ) ∧
    logKernel ((2239 / 64 : ℚ) : ℝ) ≤ ((8876414348491 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2239
  constructor
  · exact (show ((4438207174243 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((4452864798161991 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2239 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((17811459192647967 / 18446744073709551616 : ℚ) : ℝ) ≤ ((8876414348491 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2240 : ((4383829528257287 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((35 / 1 : ℚ) : ℝ) ∧
    heightZ ((35 / 1 : ℚ) : ℝ) ≤ ((17535318113029151 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((4383829528257287 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((35 / 1 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-31 / 6 : ℚ) : ℝ) ∧
      Real.exp (-((35 / 1 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-31 / 6 : ℚ) : ℝ) ≤ ((17535318113029151 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2240 : ((8603315789535 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((35 / 1 : ℚ) : ℝ) ∧
    logKernel ((35 / 1 : ℚ) : ℝ) ≤ ((2150828947385 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2240
  constructor
  · exact (show ((8603315789535 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((4383829528257287 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((35 / 1 : ℚ) : ℝ)) hh).trans
      (show zKernel ((17535318113029151 / 18446744073709551616 : ℚ) : ℝ) ≤ ((2150828947385 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2241 : ((8631729102016799 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2241 / 64 : ℚ) : ℝ) ∧
    heightZ ((2241 / 64 : ℚ) : ℝ) ≤ ((17263458204033601 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((8631729102016799 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2241 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-995 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2241 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-995 / 192 : ℚ) : ℝ) ≤ ((17263458204033601 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2241 : ((1042327448739 / 9007199254740992 : ℚ) : ℝ) ≤ logKernel ((2241 / 64 : ℚ) : ℝ) ∧
    logKernel ((2241 / 64 : ℚ) : ℝ) ≤ ((8338619589917 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2241
  constructor
  · exact (show ((1042327448739 / 9007199254740992 : ℚ) : ℝ) ≤ zKernel ((8631729102016799 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2241 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((17263458204033601 / 18446744073709551616 : ℚ) : ℝ) ≤ ((8338619589917 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2242 : ((1062238318266429 / 1152921504606846976 : ℚ) : ℝ) ≤ heightZ ((1121 / 32 : ℚ) : ℝ) ∧
    heightZ ((1121 / 32 : ℚ) : ℝ) ≤ ((16995813092262867 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((1062238318266429 / 1152921504606846976 : ℚ) : ℝ) ≤ Real.exp (-((1121 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-499 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1121 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-499 / 96 : ℚ) : ℝ) ≤ ((16995813092262867 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2242 : ((8082067236199 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1121 / 32 : ℚ) : ℝ) ∧
    logKernel ((1121 / 32 : ℚ) : ℝ) ≤ ((2020516809051 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2242
  constructor
  · exact (show ((8082067236199 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((1062238318266429 / 1152921504606846976 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1121 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((16995813092262867 / 18446744073709551616 : ℚ) : ℝ) ≤ ((2020516809051 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2243 : ((8366158716671331 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2243 / 64 : ℚ) : ℝ) ∧
    heightZ ((2243 / 64 : ℚ) : ℝ) ≤ ((16732317433342665 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((8366158716671331 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2243 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1001 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2243 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1001 / 192 : ℚ) : ℝ) ≤ ((16732317433342665 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2243 : ((1958352042149 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((2243 / 64 : ℚ) : ℝ) ∧
    logKernel ((2243 / 64 : ℚ) : ℝ) ≤ ((7833408168601 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2243
  constructor
  · exact (show ((1958352042149 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((8366158716671331 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2243 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((16732317433342665 / 18446744073709551616 : ℚ) : ℝ) ≤ ((7833408168601 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2244 : ((16472906895969331 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((561 / 16 : ℚ) : ℝ) ∧
    heightZ ((561 / 16 : ℚ) : ℝ) ≤ ((8236453447984667 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((16472906895969331 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((561 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-251 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((561 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-251 / 48 : ℚ) : ℝ) ≤ ((8236453447984667 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2244 : ((3796199768111 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((561 / 16 : ℚ) : ℝ) ∧
    logKernel ((561 / 16 : ℚ) : ℝ) ≤ ((7592399536227 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2244
  constructor
  · exact (show ((3796199768111 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((16472906895969331 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((561 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((8236453447984667 / 9223372036854775808 : ℚ) : ℝ) ≤ ((7592399536227 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2245 : ((4054379536550907 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((2245 / 64 : ℚ) : ℝ) ∧
    heightZ ((2245 / 64 : ℚ) : ℝ) ≤ ((16217518146203631 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((4054379536550907 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((2245 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1007 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2245 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1007 / 192 : ℚ) : ℝ) ≤ ((16217518146203631 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2245 : ((7358805959929 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2245 / 64 : ℚ) : ℝ) ∧
    logKernel ((2245 / 64 : ℚ) : ℝ) ≤ ((3679402979967 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2245
  constructor
  · exact (show ((7358805959929 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((4054379536550907 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2245 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((16217518146203631 / 18446744073709551616 : ℚ) : ℝ) ≤ ((3679402979967 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2246 : ((3991522208002007 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((1123 / 32 : ℚ) : ℝ) ∧
    heightZ ((1123 / 32 : ℚ) : ℝ) ≤ ((15966088832008031 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((3991522208002007 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((1123 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-505 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1123 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-505 / 96 : ℚ) : ℝ) ≤ ((15966088832008031 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2246 : ((7132399302425 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1123 / 32 : ℚ) : ℝ) ∧
    logKernel ((1123 / 32 : ℚ) : ℝ) ≤ ((3566199651215 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2246
  constructor
  · exact (show ((7132399302425 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((3991522208002007 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1123 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((15966088832008031 / 18446744073709551616 : ℚ) : ℝ) ≤ ((3566199651215 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2247 : ((7859278784011873 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2247 / 64 : ℚ) : ℝ) ∧
    heightZ ((2247 / 64 : ℚ) : ℝ) ≤ ((15718557568023749 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((7859278784011873 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2247 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1013 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2247 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1013 / 192 : ℚ) : ℝ) ≤ ((15718557568023749 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2247 : ((6912958445467 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2247 / 64 : ℚ) : ℝ) ∧
    logKernel ((2247 / 64 : ℚ) : ℝ) ≤ ((216029951421 / 2251799813685248 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2247
  constructor
  · exact (show ((6912958445467 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((7859278784011873 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2247 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((15718557568023749 / 18446744073709551616 : ℚ) : ℝ) ≤ ((216029951421 / 2251799813685248 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2248 : ((15474863920583775 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((281 / 8 : ℚ) : ℝ) ∧
    heightZ ((281 / 8 : ℚ) : ℝ) ≤ ((7737431960291889 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((15474863920583775 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((281 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-127 / 24 : ℚ) : ℝ) ∧
      Real.exp (-((281 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-127 / 24 : ℚ) : ℝ) ≤ ((7737431960291889 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2248 : ((1675067268475 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((281 / 8 : ℚ) : ℝ) ∧
    logKernel ((281 / 8 : ℚ) : ℝ) ≤ ((6700269073905 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2248
  constructor
  · exact (show ((1675067268475 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((15474863920583775 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((281 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((7737431960291889 / 9223372036854775808 : ℚ) : ℝ) ≤ ((6700269073905 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2249 : ((238046068639973 / 288230376151711744 : ℚ) : ℝ) ≤ heightZ ((2249 / 64 : ℚ) : ℝ) ∧
    heightZ ((2249 / 64 : ℚ) : ℝ) ≤ ((15234948392958275 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((238046068639973 / 288230376151711744 : ℚ) : ℝ) ≤ Real.exp (-((2249 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1019 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2249 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1019 / 192 : ℚ) : ℝ) ≤ ((15234948392958275 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2249 : ((3247061733179 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2249 / 64 : ℚ) : ℝ) ∧
    logKernel ((2249 / 64 : ℚ) : ℝ) ≤ ((6494123466363 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2249
  constructor
  · exact (show ((3247061733179 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((238046068639973 / 288230376151711744 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2249 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((15234948392958275 / 18446744073709551616 : ℚ) : ℝ) ≤ ((6494123466363 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2250 : ((3749688102707173 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((1125 / 32 : ℚ) : ℝ) ∧
    heightZ ((1125 / 32 : ℚ) : ℝ) ≤ ((14998752410828695 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((3749688102707173 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((1125 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-511 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1125 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-511 / 96 : ℚ) : ℝ) ≤ ((14998752410828695 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2250 : ((6294320292387 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1125 / 32 : ℚ) : ℝ) ∧
    logKernel ((1125 / 32 : ℚ) : ℝ) ≤ ((786790036549 / 9007199254740992 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2250
  constructor
  · exact (show ((6294320292387 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((3749688102707173 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1125 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((14998752410828695 / 18446744073709551616 : ℚ) : ℝ) ≤ ((786790036549 / 9007199254740992 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2251 : ((7383109153993563 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2251 / 64 : ℚ) : ℝ) ∧
    heightZ ((2251 / 64 : ℚ) : ℝ) ≤ ((14766218307987129 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((7383109153993563 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2251 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1025 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2251 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1025 / 192 : ℚ) : ℝ) ≤ ((14766218307987129 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2251 : ((1525166103955 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((2251 / 64 : ℚ) : ℝ) ∧
    logKernel ((2251 / 64 : ℚ) : ℝ) ≤ ((6100664415825 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2251
  constructor
  · exact (show ((1525166103955 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((7383109153993563 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2251 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((14766218307987129 / 18446744073709551616 : ℚ) : ℝ) ≤ ((6100664415825 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2252 : ((3634322328064339 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((563 / 16 : ℚ) : ℝ) ∧
    heightZ ((563 / 16 : ℚ) : ℝ) ≤ ((14537289312257359 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((3634322328064339 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((563 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-257 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((563 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-257 / 48 : ℚ) : ℝ) ≤ ((14537289312257359 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2252 : ((739120838025 / 9007199254740992 : ℚ) : ℝ) ≤ logKernel ((563 / 16 : ℚ) : ℝ) ∧
    logKernel ((563 / 16 : ℚ) : ℝ) ≤ ((5912966704205 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2252
  constructor
  · exact (show ((739120838025 / 9007199254740992 : ℚ) : ℝ) ≤ zKernel ((3634322328064339 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((563 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((14537289312257359 / 18446744073709551616 : ℚ) : ℝ) ≤ ((5912966704205 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2253 : ((14311909531634171 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2253 / 64 : ℚ) : ℝ) ∧
    heightZ ((2253 / 64 : ℚ) : ℝ) ≤ ((7155954765817087 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((14311909531634171 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2253 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1031 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2253 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1031 / 192 : ℚ) : ℝ) ≤ ((7155954765817087 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2253 : ((2865521922031 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2253 / 64 : ℚ) : ℝ) ∧
    logKernel ((2253 / 64 : ℚ) : ℝ) ≤ ((5731043844067 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2253
  constructor
  · exact (show ((2865521922031 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((14311909531634171 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2253 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((7155954765817087 / 9223372036854775808 : ℚ) : ℝ) ≤ ((5731043844067 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2254 : ((14090023940637585 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1127 / 32 : ℚ) : ℝ) ∧
    heightZ ((1127 / 32 : ℚ) : ℝ) ≤ ((3522505985159397 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((14090023940637585 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1127 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-517 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1127 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-517 / 96 : ℚ) : ℝ) ≤ ((3522505985159397 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2254 : ((2777359080953 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((1127 / 32 : ℚ) : ℝ) ∧
    logKernel ((1127 / 32 : ℚ) : ℝ) ≤ ((5554718161911 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2254
  constructor
  · exact (show ((2777359080953 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((14090023940637585 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1127 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((3522505985159397 / 4611686018427387904 : ℚ) : ℝ) ≤ ((5554718161911 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2255 : ((6935789183439303 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2255 / 64 : ℚ) : ℝ) ∧
    heightZ ((2255 / 64 : ℚ) : ℝ) ≤ ((13871578366878609 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((6935789183439303 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2255 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1037 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2255 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1037 / 192 : ℚ) : ℝ) ≤ ((13871578366878609 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2255 : ((5383817450669 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2255 / 64 : ℚ) : ℝ) ∧
    logKernel ((2255 / 64 : ℚ) : ℝ) ≤ ((2691908725337 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2255
  constructor
  · exact (show ((5383817450669 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((6935789183439303 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2255 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((13871578366878609 / 18446744073709551616 : ℚ) : ℝ) ≤ ((2691908725337 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2256 : ((6828259738916645 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((141 / 4 : ℚ) : ℝ) ∧
    heightZ ((141 / 4 : ℚ) : ℝ) ≤ ((13656519477833293 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((6828259738916645 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((141 / 4 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-65 / 12 : ℚ) : ℝ) ∧
      Real.exp (-((141 / 4 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-65 / 12 : ℚ) : ℝ) ≤ ((13656519477833293 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2256 : ((2609087400771 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((141 / 4 : ℚ) : ℝ) ∧
    logKernel ((141 / 4 : ℚ) : ℝ) ≤ ((5218174801547 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2256
  constructor
  · exact (show ((2609087400771 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((6828259738916645 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((141 / 4 : ℚ) : ℝ)) hh).trans
      (show zKernel ((13656519477833293 / 18446744073709551616 : ℚ) : ℝ) ≤ ((5218174801547 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

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

theorem log_height_bounds_384 : ((255738054049029651 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1113 / 32 : ℚ) : ℝ) ∧
    Real.log ((1113 / 32 : ℚ) : ℝ) ≤ ((127869027024514827 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((255738054049029651 / 72057594037927936 : ℚ) : ℝ) ≤ ((1113 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1113 / 32 : ℚ) : ℝ) ≤ Real.exp ((127869027024514827 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_384 : heightPower (384 : Fin 988) ≤ ((54445207312675 / 8796093022208 : ℚ) : ℝ) := by
  have hh := log_height_bounds_384
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_384 : heightFactor (384 : Fin 988) ≤ ((7866743809973 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_384
  obtain ⟨hpl, hph⟩ := kernel_bounds_2225
  obtain ⟨hcl, hch⟩ := kernel_bounds_2226
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2226
  have h : (((1238769 / 512 : ℚ) : ℝ) * (logKernel ((2225 / 64 : ℚ) : ℝ) - logKernel ((1113 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1113 / 32 : ℚ) : ℝ) + Real.log ((1113 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((7866743809973 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_385 : ((255770417666927353 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2227 / 64 : ℚ) : ℝ) ∧
    Real.log ((2227 / 64 : ℚ) : ℝ) ≤ ((63942604416731839 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((255770417666927353 / 72057594037927936 : ℚ) : ℝ) ≤ ((2227 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2227 / 64 : ℚ) : ℝ) ≤ Real.exp ((63942604416731839 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_385 : heightPower (385 : Fin 988) ≤ ((436692775224779 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_385
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_385 : heightFactor (385 : Fin 988) ≤ ((15345123346571 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_385
  obtain ⟨hpl, hph⟩ := kernel_bounds_2226
  obtain ⟨hcl, hch⟩ := kernel_bounds_2227
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2227
  have h : (((4959529 / 2048 : ℚ) : ℝ) * (logKernel ((1113 / 32 : ℚ) : ℝ) - logKernel ((2227 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2227 / 64 : ℚ) : ℝ) + Real.log ((2227 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((15345123346571 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_386 : ((255802766755703175 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((557 / 16 : ℚ) : ℝ) ∧
    Real.log ((557 / 16 : ℚ) : ℝ) ≤ ((127901383377851589 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((255802766755703175 / 72057594037927936 : ℚ) : ℝ) ≤ ((557 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((557 / 16 : ℚ) : ℝ) ≤ Real.exp ((127901383377851589 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_386 : heightPower (386 : Fin 988) ≤ ((1751295511038251 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_386
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_386 : heightFactor (386 : Fin 988) ≤ ((14966338387635 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_386
  obtain ⟨hpl, hph⟩ := kernel_bounds_2227
  obtain ⟨hcl, hch⟩ := kernel_bounds_2228
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2228
  have h : (((310249 / 128 : ℚ) : ℝ) * (logKernel ((2227 / 64 : ℚ) : ℝ) - logKernel ((557 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((557 / 16 : ℚ) : ℝ) + Real.log ((557 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((14966338387635 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_387 : ((255835101328396493 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2229 / 64 : ℚ) : ℝ) ∧
    Real.log ((2229 / 64 : ℚ) : ℝ) ≤ ((15989693833024781 / 4503599627370496 : ℚ) : ℝ) := by
  have hl : Real.exp ((255835101328396493 / 72057594037927936 : ℚ) : ℝ) ≤ ((2229 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2229 / 64 : ℚ) : ℝ) ≤ Real.exp ((15989693833024781 / 4503599627370496 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_387 : heightPower (387 : Fin 988) ≤ ((877909932236969 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_387
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_387 : heightFactor (387 : Fin 988) ≤ ((7298448320909 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_387
  obtain ⟨hpl, hph⟩ := kernel_bounds_2228
  obtain ⟨hcl, hch⟩ := kernel_bounds_2229
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2229
  have h : (((4968441 / 2048 : ℚ) : ℝ) * (logKernel ((557 / 16 : ℚ) : ℝ) - logKernel ((2229 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2229 / 64 : ℚ) : ℝ) + Real.log ((2229 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((7298448320909 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_388 : ((127933710699014567 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((1115 / 32 : ℚ) : ℝ) ∧
    Real.log ((1115 / 32 : ℚ) : ℝ) ≤ ((255867421398029137 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((127933710699014567 / 36028797018963968 : ℚ) : ℝ) ≤ ((1115 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1115 / 32 : ℚ) : ℝ) ≤ Real.exp ((255867421398029137 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_388 : heightPower (388 : Fin 988) ≤ ((1760344161257045 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_388
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_388 : heightFactor (388 : Fin 988) ≤ ((28473135644761 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_388
  obtain ⟨hpl, hph⟩ := kernel_bounds_2229
  obtain ⟨hcl, hch⟩ := kernel_bounds_2230
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2230
  have h : (((1243225 / 512 : ℚ) : ℝ) * (logKernel ((2229 / 64 : ℚ) : ℝ) - logKernel ((1115 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1115 / 32 : ℚ) : ℝ) + Real.log ((1115 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((28473135644761 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_389 : ((127949863488802707 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2231 / 64 : ℚ) : ℝ) ∧
    Real.log ((2231 / 64 : ℚ) : ℝ) ≤ ((255899726977605417 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((127949863488802707 / 36028797018963968 : ℚ) : ℝ) ≤ ((2231 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2231 / 64 : ℚ) : ℝ) ≤ Real.exp ((255899726977605417 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_389 : heightPower (389 : Fin 988) ≤ ((1764868401438369 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_389
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_389 : heightFactor (389 : Fin 988) ≤ ((27770254628169 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_389
  obtain ⟨hpl, hph⟩ := kernel_bounds_2230
  obtain ⟨hcl, hch⟩ := kernel_bounds_2231
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2231
  have h : (((4977361 / 2048 : ℚ) : ℝ) * (logKernel ((1115 / 32 : ℚ) : ℝ) - logKernel ((2231 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2231 / 64 : ℚ) : ℝ) + Real.log ((2231 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((27770254628169 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_390 : ((255932018080112163 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((279 / 8 : ℚ) : ℝ) ∧
    Real.log ((279 / 8 : ℚ) : ℝ) ≤ ((127966009040056083 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((255932018080112163 / 72057594037927936 : ℚ) : ℝ) ≤ ((279 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((279 / 8 : ℚ) : ℝ) ≤ Real.exp ((127966009040056083 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_390 : heightPower (390 : Fin 988) ≤ ((55293518283395 / 8796093022208 : ℚ) : ℝ) := by
  have hh := log_height_bounds_390
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_390 : heightFactor (390 : Fin 988) ≤ ((27084712067257 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_390
  obtain ⟨hpl, hph⟩ := kernel_bounds_2231
  obtain ⟨hcl, hch⟩ := kernel_bounds_2232
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2232
  have h : (((77841 / 32 : ℚ) : ℝ) * (logKernel ((2231 / 64 : ℚ) : ℝ) - logKernel ((279 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((279 / 8 : ℚ) : ℝ) + Real.log ((279 / 8 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((27084712067257 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_391 : ((31995536839814845 / 9007199254740992 : ℚ) : ℝ) ≤ Real.log ((2233 / 64 : ℚ) : ℝ) ∧
    Real.log ((2233 / 64 : ℚ) : ℝ) ≤ ((255964294718518763 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((31995536839814845 / 9007199254740992 : ℚ) : ℝ) ≤ ((2233 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2233 / 64 : ℚ) : ℝ) ≤ Real.exp ((255964294718518763 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_391 : heightPower (391 : Fin 988) ≤ ((1773916712198519 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_391
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_391 : heightFactor (391 : Fin 988) ≤ ((26416080587039 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_391
  obtain ⟨hpl, hph⟩ := kernel_bounds_2232
  obtain ⟨hcl, hch⟩ := kernel_bounds_2233
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2233
  have h : (((4986289 / 2048 : ℚ) : ℝ) * (logKernel ((279 / 8 : ℚ) : ℝ) - logKernel ((2233 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2233 / 64 : ℚ) : ℝ) + Real.log ((2233 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((26416080587039 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_392 : ((255996556905777167 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1117 / 32 : ℚ) : ℝ) ∧
    Real.log ((1117 / 32 : ℚ) : ℝ) ≤ ((127998278452888585 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((255996556905777167 / 72057594037927936 : ℚ) : ℝ) ≤ ((1117 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1117 / 32 : ℚ) : ℝ) ≤ Real.exp ((127998278452888585 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_392 : heightPower (392 : Fin 988) ≤ ((889220391439301 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_392
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_392 : heightFactor (392 : Fin 988) ≤ ((25763943338569 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_392
  obtain ⟨hpl, hph⟩ := kernel_bounds_2233
  obtain ⟨hcl, hch⟩ := kernel_bounds_2234
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2234
  have h : (((1247689 / 512 : ℚ) : ℝ) * (logKernel ((2233 / 64 : ℚ) : ℝ) - logKernel ((1117 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1117 / 32 : ℚ) : ℝ) + Real.log ((1117 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((25763943338569 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_393 : ((256028804654821953 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2235 / 64 : ℚ) : ℝ) ∧
    Real.log ((2235 / 64 : ℚ) : ℝ) ≤ ((64007201163705489 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((256028804654821953 / 72057594037927936 : ℚ) : ℝ) ≤ ((2235 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2235 / 64 : ℚ) : ℝ) ≤ Real.exp ((64007201163705489 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_393 : heightPower (393 : Fin 988) ≤ ((445741199289853 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_393
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_393 : heightFactor (393 : Fin 988) ≤ ((6281973434977 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_393
  obtain ⟨hpl, hph⟩ := kernel_bounds_2234
  obtain ⟨hcl, hch⟩ := kernel_bounds_2235
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2235
  have h : (((4995225 / 2048 : ℚ) : ℝ) * (logKernel ((1117 / 32 : ℚ) : ℝ) - logKernel ((2235 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2235 / 64 : ℚ) : ℝ) + Real.log ((2235 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((6281973434977 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_394 : ((128030518989285165 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((559 / 16 : ℚ) : ℝ) ∧
    Real.log ((559 / 16 : ℚ) : ℝ) ≤ ((256061037978570333 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((128030518989285165 / 36028797018963968 : ℚ) : ℝ) ≤ ((559 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((559 / 16 : ℚ) : ℝ) ≤ Real.exp ((256061037978570333 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_394 : heightPower (394 : Fin 988) ≤ ((111718047193213 / 17592186044416 : ℚ) : ℝ) := by
  have hh := log_height_bounds_394
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_394 : heightFactor (394 : Fin 988) ≤ ((24507535223453 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_394
  obtain ⟨hpl, hph⟩ := kernel_bounds_2235
  obtain ⟨hcl, hch⟩ := kernel_bounds_2236
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2236
  have h : (((312481 / 128 : ℚ) : ℝ) * (logKernel ((2235 / 64 : ℚ) : ℝ) - logKernel ((559 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((559 / 16 : ℚ) : ℝ) + Real.log ((559 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((24507535223453 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_395 : ((128046628444961093 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2237 / 64 : ℚ) : ℝ) ∧
    Real.log ((2237 / 64 : ℚ) : ℝ) ≤ ((256093256889922189 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((128046628444961093 / 36028797018963968 : ℚ) : ℝ) ≤ ((2237 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2237 / 64 : ℚ) : ℝ) ≤ Real.exp ((256093256889922189 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_395 : heightPower (395 : Fin 988) ≤ ((448003164181245 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_395
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_395 : heightFactor (395 : Fin 988) ≤ ((23902480989479 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_395
  obtain ⟨hpl, hph⟩ := kernel_bounds_2236
  obtain ⟨hcl, hch⟩ := kernel_bounds_2237
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2237
  have h : (((5004169 / 2048 : ℚ) : ℝ) * (logKernel ((559 / 16 : ℚ) : ℝ) - logKernel ((2237 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2237 / 64 : ℚ) : ℝ) + Real.log ((2237 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((23902480989479 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_396 : ((64031365350440027 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((1119 / 32 : ℚ) : ℝ) ∧
    Real.log ((1119 / 32 : ℚ) : ℝ) ≤ ((256125461401760111 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((64031365350440027 / 18014398509481984 : ℚ) : ℝ) ≤ ((1119 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1119 / 32 : ℚ) : ℝ) ≤ Real.exp ((256125461401760111 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_396 : heightPower (396 : Fin 988) ≤ ((1796536502110451 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_396
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_396 : heightFactor (396 : Fin 988) ≤ ((11656176882871 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_396
  obtain ⟨hpl, hph⟩ := kernel_bounds_2237
  obtain ⟨hcl, hch⟩ := kernel_bounds_2238
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2238
  have h : (((1252161 / 512 : ℚ) : ℝ) * (logKernel ((2237 / 64 : ℚ) : ℝ) - logKernel ((1119 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1119 / 32 : ℚ) : ℝ) + Real.log ((1119 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((11656176882871 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_397 : ((128078825763474711 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2239 / 64 : ℚ) : ℝ) ∧
    Real.log ((2239 / 64 : ℚ) : ℝ) ≤ ((256157651526949425 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((128078825763474711 / 36028797018963968 : ℚ) : ℝ) ≤ ((2239 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2239 / 64 : ℚ) : ℝ) ≤ Real.exp ((256157651526949425 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_397 : heightPower (397 : Fin 988) ≤ ((450265072824519 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_397
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_397 : heightFactor (397 : Fin 988) ≤ ((22736785572997 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_397
  obtain ⟨hpl, hph⟩ := kernel_bounds_2238
  obtain ⟨hcl, hch⟩ := kernel_bounds_2239
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2239
  have h : (((5013121 / 2048 : ℚ) : ℝ) * (logKernel ((1119 / 32 : ℚ) : ℝ) - logKernel ((2239 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2239 / 64 : ℚ) : ℝ) + Real.log ((2239 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((22736785572997 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_398 : ((128094913639169109 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((35 / 1 : ℚ) : ℝ) ∧
    Real.log ((35 / 1 : ℚ) : ℝ) ≤ ((256189827278338221 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((128094913639169109 / 36028797018963968 : ℚ) : ℝ) ≤ ((35 / 1 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((35 / 1 : ℚ) : ℝ) ≤ Real.exp ((256189827278338221 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_398 : heightPower (398 : Fin 988) ≤ ((902792012169021 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_398
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_398 : heightFactor (398 : Fin 988) ≤ ((11087708748137 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_398
  obtain ⟨hpl, hph⟩ := kernel_bounds_2239
  obtain ⟨hcl, hch⟩ := kernel_bounds_2240
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2240
  have h : (((2450 / 1 : ℚ) : ℝ) * (logKernel ((2239 / 64 : ℚ) : ℝ) - logKernel ((35 / 1 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((35 / 1 : ℚ) : ℝ) + Real.log ((35 / 1 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((11087708748137 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_399 : ((32027748583594673 / 9007199254740992 : ℚ) : ℝ) ≤ Real.log ((2241 / 64 : ℚ) : ℝ) ∧
    Real.log ((2241 / 64 : ℚ) : ℝ) ≤ ((256221988668757387 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((32027748583594673 / 9007199254740992 : ℚ) : ℝ) ≤ ((2241 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2241 / 64 : ℚ) : ℝ) ≤ Real.exp ((256221988668757387 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_399 : heightPower (399 : Fin 988) ≤ ((1810107701280471 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_399
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_399 : heightFactor (399 : Fin 988) ≤ ((5406974865447 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_399
  obtain ⟨hpl, hph⟩ := kernel_bounds_2240
  obtain ⟨hcl, hch⟩ := kernel_bounds_2241
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2241
  have h : (((5022081 / 2048 : ℚ) : ℝ) * (logKernel ((35 / 1 : ℚ) : ℝ) - logKernel ((2241 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2241 / 64 : ℚ) : ℝ) + Real.log ((2241 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((5406974865447 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_400 : ((128127067855510317 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((1121 / 32 : ℚ) : ℝ) ∧
    Real.log ((1121 / 32 : ℚ) : ℝ) ≤ ((256254135711020637 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((128127067855510317 / 36028797018963968 : ℚ) : ℝ) ≤ ((1121 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1121 / 32 : ℚ) : ℝ) ≤ Real.exp ((256254135711020637 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_400 : heightPower (400 : Fin 988) ≤ ((226828915271927 / 35184372088832 : ℚ) : ℝ) := by
  have hh := log_height_bounds_400
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_400 : heightFactor (400 : Fin 988) ≤ ((21093890019327 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_400
  obtain ⟨hpl, hph⟩ := kernel_bounds_2241
  obtain ⟨hcl, hch⟩ := kernel_bounds_2242
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2242
  have h : (((1256641 / 512 : ℚ) : ℝ) * (logKernel ((2241 / 64 : ℚ) : ℝ) - logKernel ((1121 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1121 / 32 : ℚ) : ℝ) + Real.log ((1121 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((21093890019327 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_401 : ((64071567104481135 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((2243 / 64 : ℚ) : ℝ) ∧
    Real.log ((2243 / 64 : ℚ) : ℝ) ≤ ((256286268417924543 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((64071567104481135 / 18014398509481984 : ℚ) : ℝ) ≤ ((2243 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2243 / 64 : ℚ) : ℝ) ≤ Real.exp ((256286268417924543 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_401 : heightPower (401 : Fin 988) ≤ ((1819154887072863 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_401
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_401 : heightFactor (401 : Fin 988) ≤ ((1285816008125 / 17592186044416 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_401
  obtain ⟨hpl, hph⟩ := kernel_bounds_2242
  obtain ⟨hcl, hch⟩ := kernel_bounds_2243
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2243
  have h : (((5031049 / 2048 : ℚ) : ℝ) * (logKernel ((1121 / 32 : ℚ) : ℝ) - logKernel ((2243 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2243 / 64 : ℚ) : ℝ) + Real.log ((2243 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1285816008125 / 17592186044416 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_402 : ((128159193401124281 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((561 / 16 : ℚ) : ℝ) ∧
    Real.log ((561 / 16 : ℚ) : ℝ) ≤ ((256318386802248565 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((128159193401124281 / 36028797018963968 : ℚ) : ℝ) ≤ ((561 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((561 / 16 : ℚ) : ℝ) ≤ Real.exp ((256318386802248565 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_402 : heightPower (402 : Fin 988) ≤ ((1823678396022733 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_402
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_402 : heightFactor (402 : Fin 988) ≤ ((10032536479597 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_402
  obtain ⟨hpl, hph⟩ := kernel_bounds_2243
  obtain ⟨hcl, hch⟩ := kernel_bounds_2244
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2244
  have h : (((314721 / 128 : ℚ) : ℝ) * (logKernel ((2243 / 64 : ℚ) : ℝ) - logKernel ((561 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((561 / 16 : ℚ) : ℝ) + Real.log ((561 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((10032536479597 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_403 : ((256350490876755081 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2245 / 64 : ℚ) : ℝ) ∧
    Real.log ((2245 / 64 : ℚ) : ℝ) ≤ ((64087622719188771 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((256350490876755081 / 72057594037927936 : ℚ) : ℝ) ≤ ((2245 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2245 / 64 : ℚ) : ℝ) ≤ Real.exp ((64087622719188771 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_403 : heightPower (403 : Fin 988) ≤ ((914100924537439 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_403
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_403 : heightFactor (403 : Fin 988) ≤ ((2446202959329 / 35184372088832 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_403
  obtain ⟨hpl, hph⟩ := kernel_bounds_2244
  obtain ⟨hcl, hch⟩ := kernel_bounds_2245
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2245
  have h : (((5040025 / 2048 : ℚ) : ℝ) * (logKernel ((561 / 16 : ℚ) : ℝ) - logKernel ((2245 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2245 / 64 : ℚ) : ℝ) + Real.log ((2245 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((2446202959329 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_404 : ((256382580654189425 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1123 / 32 : ℚ) : ℝ) ∧
    Real.log ((1123 / 32 : ℚ) : ℝ) ≤ ((64095645163547357 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((256382580654189425 / 72057594037927936 : ℚ) : ℝ) ≤ ((1123 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1123 / 32 : ℚ) : ℝ) ≤ Real.exp ((64095645163547357 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_404 : heightPower (404 : Fin 988) ≤ ((1832725246279085 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_404
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_404 : heightFactor (404 : Fin 988) ≤ ((19086399249395 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_404
  obtain ⟨hpl, hph⟩ := kernel_bounds_2245
  obtain ⟨hcl, hch⟩ := kernel_bounds_2246
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2246
  have h : (((1261129 / 512 : ℚ) : ℝ) * (logKernel ((2245 / 64 : ℚ) : ℝ) - logKernel ((1123 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1123 / 32 : ℚ) : ℝ) + Real.log ((1123 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((19086399249395 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_405 : ((8012958004602497 / 2251799813685248 : ℚ) : ℝ) ≤ Real.log ((2247 / 64 : ℚ) : ℝ) ∧
    Real.log ((2247 / 64 : ℚ) : ℝ) ≤ ((256414656147279907 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((8012958004602497 / 2251799813685248 : ℚ) : ℝ) ≤ ((2247 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2247 / 64 : ℚ) : ℝ) ≤ Real.exp ((256414656147279907 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_405 : heightPower (405 : Fin 988) ≤ ((918624293842537 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_405
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_405 : heightFactor (405 : Fin 988) ≤ ((18615098269787 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_405
  obtain ⟨hpl, hph⟩ := kernel_bounds_2246
  obtain ⟨hcl, hch⟩ := kernel_bounds_2247
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2247
  have h : (((5049009 / 2048 : ℚ) : ℝ) * (logKernel ((1123 / 32 : ℚ) : ℝ) - logKernel ((2247 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2247 / 64 : ℚ) : ℝ) + Real.log ((2247 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((18615098269787 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_406 : ((256446717368737835 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((281 / 8 : ℚ) : ℝ) ∧
    Real.log ((281 / 8 : ℚ) : ℝ) ≤ ((128223358684368919 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((256446717368737835 / 72057594037927936 : ℚ) : ℝ) ≤ ((281 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((281 / 8 : ℚ) : ℝ) ≤ Real.exp ((128223358684368919 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_406 : heightPower (406 : Fin 988) ≤ ((920885936671249 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_406
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_406 : heightFactor (406 : Fin 988) ≤ ((9077713373963 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_406
  obtain ⟨hpl, hph⟩ := kernel_bounds_2247
  obtain ⟨hcl, hch⟩ := kernel_bounds_2248
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2248
  have h : (((78961 / 32 : ℚ) : ℝ) * (logKernel ((2247 / 64 : ℚ) : ℝ) - logKernel ((281 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((281 / 8 : ℚ) : ℝ) + Real.log ((281 / 8 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((9077713373963 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_407 : ((256478764331257579 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2249 / 64 : ℚ) : ℝ) ∧
    Real.log ((2249 / 64 : ℚ) : ℝ) ≤ ((128239382165628791 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((256478764331257579 / 72057594037927936 : ℚ) : ℝ) ≤ ((2249 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2249 / 64 : ℚ) : ℝ) ≤ Real.exp ((128239382165628791 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_407 : heightPower (407 : Fin 988) ≤ ((115393443956309 / 17592186044416 : ℚ) : ℝ) := by
  have hh := log_height_bounds_407
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_407 : heightFactor (407 : Fin 988) ≤ ((8853548969473 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_407
  obtain ⟨hpl, hph⟩ := kernel_bounds_2248
  obtain ⟨hcl, hch⟩ := kernel_bounds_2249
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2249
  have h : (((5058001 / 2048 : ℚ) : ℝ) * (logKernel ((281 / 8 : ℚ) : ℝ) - logKernel ((2249 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2249 / 64 : ℚ) : ℝ) + Real.log ((2249 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((8853548969473 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_408 : ((256510797047516565 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1125 / 32 : ℚ) : ℝ) ∧
    Real.log ((1125 / 32 : ℚ) : ℝ) ≤ ((32063849630939571 / 9007199254740992 : ℚ) : ℝ) := by
  have hl : Real.exp ((256510797047516565 / 72057594037927936 : ℚ) : ℝ) ≤ ((1125 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1125 / 32 : ℚ) : ℝ) ≤ Real.exp ((32063849630939571 / 9007199254740992 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_408 : heightPower (408 : Fin 988) ≤ ((1850818277609935 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_408
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_408 : heightFactor (408 : Fin 988) ≤ ((8634916081347 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_408
  obtain ⟨hpl, hph⟩ := kernel_bounds_2249
  obtain ⟨hcl, hch⟩ := kernel_bounds_2250
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2250
  have h : (((1265625 / 512 : ℚ) : ℝ) * (logKernel ((2249 / 64 : ℚ) : ℝ) - logKernel ((1125 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1125 / 32 : ℚ) : ℝ) + Real.log ((1125 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((8634916081347 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_409 : ((256542815530175323 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2251 / 64 : ℚ) : ℝ) ∧
    Real.log ((2251 / 64 : ℚ) : ℝ) ≤ ((128271407765087663 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((256542815530175323 / 72057594037927936 : ℚ) : ℝ) ≤ ((2251 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2251 / 64 : ℚ) : ℝ) ≤ Real.exp ((128271407765087663 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_409 : heightPower (409 : Fin 988) ≤ ((1855341396318925 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_409
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_409 : heightFactor (409 : Fin 988) ≤ ((16843356629811 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_409
  obtain ⟨hpl, hph⟩ := kernel_bounds_2250
  obtain ⟨hcl, hch⟩ := kernel_bounds_2251
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2251
  have h : (((5067001 / 2048 : ℚ) : ℝ) * (logKernel ((1125 / 32 : ℚ) : ℝ) - logKernel ((2251 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2251 / 64 : ℚ) : ℝ) + Real.log ((2251 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((16843356629811 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_410 : ((256574819791877513 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((563 / 16 : ℚ) : ℝ) ∧
    Real.log ((563 / 16 : ℚ) : ℝ) ≤ ((64143704947969379 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((256574819791877513 / 72057594037927936 : ℚ) : ℝ) ≤ ((563 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((563 / 16 : ℚ) : ℝ) ≤ Real.exp ((64143704947969379 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_410 : heightPower (410 : Fin 988) ≤ ((1859864459477303 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_410
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_410 : heightFactor (410 : Fin 988) ≤ ((8213702636047 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_410
  obtain ⟨hpl, hph⟩ := kernel_bounds_2251
  obtain ⟨hcl, hch⟩ := kernel_bounds_2252
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2252
  have h : (((316969 / 128 : ℚ) : ℝ) * (logKernel ((2251 / 64 : ℚ) : ℝ) - logKernel ((563 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((563 / 16 : ℚ) : ℝ) + Real.log ((563 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((8213702636047 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_411 : ((256606809845249957 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2253 / 64 : ℚ) : ℝ) ∧
    Real.log ((2253 / 64 : ℚ) : ℝ) ≤ ((32075851230656245 / 9007199254740992 : ℚ) : ℝ) := by
  have hl : Real.exp ((256606809845249957 / 72057594037927936 : ℚ) : ℝ) ≤ ((2253 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2253 / 64 : ℚ) : ℝ) ≤ Real.exp ((32075851230656245 / 9007199254740992 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_411 : heightPower (411 : Fin 988) ≤ ((1864387467134393 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_411
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_411 : heightFactor (411 : Fin 988) ≤ ((8010859288515 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_411
  obtain ⟨hpl, hph⟩ := kernel_bounds_2252
  obtain ⟨hcl, hch⟩ := kernel_bounds_2253
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2253
  have h : (((5076009 / 2048 : ℚ) : ℝ) * (logKernel ((563 / 16 : ℚ) : ℝ) - logKernel ((2253 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2253 / 64 : ℚ) : ℝ) + Real.log ((2253 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((8010859288515 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_412 : ((128319392851451333 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((1127 / 32 : ℚ) : ℝ) ∧
    Real.log ((1127 / 32 : ℚ) : ℝ) ≤ ((256638785702902669 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((128319392851451333 / 36028797018963968 : ℚ) : ℝ) ≤ ((1127 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1127 / 32 : ℚ) : ℝ) ≤ Real.exp ((256638785702902669 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_412 : heightPower (412 : Fin 988) ≤ ((1868910419339453 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_412
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_412 : heightFactor (412 : Fin 988) ≤ ((15626043426399 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_412
  obtain ⟨hpl, hph⟩ := kernel_bounds_2253
  obtain ⟨hcl, hch⟩ := kernel_bounds_2254
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2254
  have h : (((1270129 / 512 : ℚ) : ℝ) * (logKernel ((2253 / 64 : ℚ) : ℝ) - logKernel ((1127 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1127 / 32 : ℚ) : ℝ) + Real.log ((1127 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((15626043426399 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_413 : ((32083843422178609 / 9007199254740992 : ℚ) : ℝ) ≤ Real.log ((2255 / 64 : ℚ) : ℝ) ∧
    Real.log ((2255 / 64 : ℚ) : ℝ) ≤ ((256670747377428875 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((32083843422178609 / 9007199254740992 : ℚ) : ℝ) ≤ ((2255 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2255 / 64 : ℚ) : ℝ) ≤ Real.exp ((256670747377428875 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_413 : heightPower (413 : Fin 988) ≤ ((1873433316141675 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_413
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_413 : heightFactor (413 : Fin 988) ≤ ((15240132938843 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_413
  obtain ⟨hpl, hph⟩ := kernel_bounds_2254
  obtain ⟨hcl, hch⟩ := kernel_bounds_2255
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2255
  have h : (((5085025 / 2048 : ℚ) : ℝ) * (logKernel ((1127 / 32 : ℚ) : ℝ) - logKernel ((2255 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2255 / 64 : ℚ) : ℝ) + Real.log ((2255 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((15240132938843 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_414 : ((2005489803760977 / 562949953421312 : ℚ) : ℝ) ≤ Real.log ((141 / 4 : ℚ) : ℝ) ∧
    Real.log ((141 / 4 : ℚ) : ℝ) ≤ ((256702694881405059 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((2005489803760977 / 562949953421312 : ℚ) : ℝ) ≤ ((141 / 4 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((141 / 4 : ℚ) : ℝ) ≤ Real.exp ((256702694881405059 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_414 : heightPower (414 : Fin 988) ≤ ((938978078795093 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_414
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_414 : heightFactor (414 : Fin 988) ≤ ((7431873158161 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_414
  obtain ⟨hpl, hph⟩ := kernel_bounds_2255
  obtain ⟨hcl, hch⟩ := kernel_bounds_2256
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2256
  have h : (((19881 / 8 : ℚ) : ℝ) * (logKernel ((2255 / 64 : ℚ) : ℝ) - logKernel ((141 / 4 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((141 / 4 : ℚ) : ℝ) + Real.log ((141 / 4 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((7431873158161 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_415 : ((64183657056847745 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((2257 / 64 : ℚ) : ℝ) ∧
    Real.log ((2257 / 64 : ℚ) : ℝ) ≤ ((256734628227390983 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((64183657056847745 / 18014398509481984 : ℚ) : ℝ) ≤ ((2257 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2257 / 64 : ℚ) : ℝ) ≤ Real.exp ((256734628227390983 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_415 : heightPower (415 : Fin 988) ≤ ((58827466991689 / 8796093022208 : ℚ) : ℝ) := by
  have hh := log_height_bounds_415
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_415 : heightFactor (415 : Fin 988) ≤ ((14496648694327 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_415
  obtain ⟨hpl, hph⟩ := kernel_bounds_2256
  obtain ⟨hcl, hch⟩ := kernel_bounds_2257
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2257
  have h : (((5094049 / 2048 : ℚ) : ℝ) * (logKernel ((141 / 4 : ℚ) : ℝ) - logKernel ((2257 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2257 / 64 : ℚ) : ℝ) + Real.log ((2257 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((14496648694327 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

end LegendreK6.M2Pilot.Enclosures.Height012
