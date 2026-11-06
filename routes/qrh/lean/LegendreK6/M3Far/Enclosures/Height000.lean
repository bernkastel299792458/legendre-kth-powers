import LegendreK6.M3FarDefinitions
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp

/-! Generated proposals: every bound is checked by Lean, not by trusting Arb. -/
namespace LegendreK6.M3Far.Enclosures.Height000
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem height_z_bounds_795 : ((9171432782795317875 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((795 / 8 : ℚ) : ℝ) ∧
    heightZ ((795 / 8 : ℚ) : ℝ) ≤ ((4585716391397658939 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((9171432782795317875 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((795 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((11 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((795 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((11 / 16 : ℚ) : ℝ) ≤ ((4585716391397658939 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_795 : ((36028797018963967 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((795 / 8 : ℚ) : ℝ) ∧
    logKernel ((795 / 8 : ℚ) : ℝ) ≤ ((36028797018963969 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_795
  constructor
  · exact (show ((36028797018963967 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((9171432782795317875 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((795 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((4585716391397658939 / 9223372036854775808 : ℚ) : ℝ) ≤ ((36028797018963969 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_796 : ((8093761023079684367 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((199 / 2 : ℚ) : ℝ) ∧
    heightZ ((199 / 2 : ℚ) : ℝ) ≤ ((4046880511539842185 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((8093761023079684367 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((199 / 2 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((9 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((199 / 2 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((9 / 16 : ℚ) : ℝ) ≤ ((4046880511539842185 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_796 : ((32636133157579371 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((199 / 2 : ℚ) : ℝ) ∧
    logKernel ((199 / 2 : ℚ) : ℝ) ≤ ((65272266315158747 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_796
  constructor
  · exact (show ((32636133157579371 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((8093761023079684367 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((199 / 2 : ℚ) : ℝ)) hh).trans
      (show zKernel ((4046880511539842185 / 9223372036854775808 : ℚ) : ℝ) ≤ ((65272266315158747 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_797 : ((7142719033127747439 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((797 / 8 : ℚ) : ℝ) ∧
    heightZ ((797 / 8 : ℚ) : ℝ) ≤ ((3571359516563873721 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((7142719033127747439 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((797 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((7 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((797 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((7 / 16 : ℚ) : ℝ) ≤ ((3571359516563873721 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_797 : ((14400643211951103 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((797 / 8 : ℚ) : ℝ) ∧
    logKernel ((797 / 8 : ℚ) : ℝ) ≤ ((57602572847804417 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_797
  constructor
  · exact (show ((14400643211951103 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((7142719033127747439 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((797 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((3571359516563873721 / 9223372036854775808 : ℚ) : ℝ) ≤ ((57602572847804417 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_798 : ((1575856855691818299 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((399 / 4 : ℚ) : ℝ) ∧
    heightZ ((399 / 4 : ℚ) : ℝ) ≤ ((6303427422767273199 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((1575856855691818299 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((399 / 4 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((5 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((399 / 4 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((5 / 16 : ℚ) : ℝ) ≤ ((6303427422767273199 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_798 : ((25417046059545455 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((399 / 4 : ℚ) : ℝ) ∧
    logKernel ((399 / 4 : ℚ) : ℝ) ≤ ((50834092119090915 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_798
  constructor
  · exact (show ((25417046059545455 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((1575856855691818299 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((399 / 4 : ℚ) : ℝ)) hh).trans
      (show zKernel ((6303427422767273199 / 18446744073709551616 : ℚ) : ℝ) ≤ ((50834092119090915 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_799 : ((1390688794064729389 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((799 / 8 : ℚ) : ℝ) ∧
    heightZ ((799 / 8 : ℚ) : ℝ) ≤ ((5562755176258917559 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((1390688794064729389 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((799 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((3 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((799 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((3 / 16 : ℚ) : ℝ) ≤ ((5562755176258917559 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_799 : ((5607616105099715 / 9007199254740992 : ℚ) : ℝ) ≤ logKernel ((799 / 8 : ℚ) : ℝ) ∧
    logKernel ((799 / 8 : ℚ) : ℝ) ≤ ((44860928840797725 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_799
  constructor
  · exact (show ((5607616105099715 / 9007199254740992 : ℚ) : ℝ) ≤ zKernel ((1390688794064729389 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((799 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((5562755176258917559 / 18446744073709551616 : ℚ) : ℝ) ≤ ((44860928840797725 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_800 : ((1227278553221229949 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((100 / 1 : ℚ) : ℝ) ∧
    heightZ ((100 / 1 : ℚ) : ℝ) ≤ ((4909114212884919799 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((1227278553221229949 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((100 / 1 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((1 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((100 / 1 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((1 / 16 : ℚ) : ℝ) ≤ ((4909114212884919799 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_800 : ((39589630749071931 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((100 / 1 : ℚ) : ℝ) ∧
    logKernel ((100 / 1 : ℚ) : ℝ) ≤ ((618587980454249 / 1125899906842624 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_800
  constructor
  · exact (show ((39589630749071931 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((1227278553221229949 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((100 / 1 : ℚ) : ℝ)) hh).trans
      (show zKernel ((4909114212884919799 / 18446744073709551616 : ℚ) : ℝ) ≤ ((618587980454249 / 1125899906842624 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_801 : ((4332278087304955803 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((801 / 8 : ℚ) : ℝ) ∧
    heightZ ((801 / 8 : ℚ) : ℝ) ≤ ((2166139043652477903 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((4332278087304955803 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((801 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-1 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((801 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-1 / 16 : ℚ) : ℝ) ≤ ((2166139043652477903 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_801 : ((34937726510523835 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((801 / 8 : ℚ) : ℝ) ∧
    logKernel ((801 / 8 : ℚ) : ℝ) ≤ ((545901976726935 / 1125899906842624 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_801
  constructor
  · exact (show ((34937726510523835 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((4332278087304955803 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((801 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((2166139043652477903 / 9223372036854775808 : ℚ) : ℝ) ≤ ((545901976726935 / 1125899906842624 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_802 : ((3823221993181738879 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((401 / 4 : ℚ) : ℝ) ∧
    heightZ ((401 / 4 : ℚ) : ℝ) ≤ ((1911610996590869441 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((3823221993181738879 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((401 / 4 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-3 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((401 / 4 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-3 / 16 : ℚ) : ℝ) ≤ ((1911610996590869441 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_802 : ((7708108857221247 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((401 / 4 : ℚ) : ℝ) ∧
    logKernel ((401 / 4 : ℚ) : ℝ) ≤ ((30832435428884993 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_802
  constructor
  · exact (show ((7708108857221247 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((3823221993181738879 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((401 / 4 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1911610996590869441 / 9223372036854775808 : ℚ) : ℝ) ≤ ((30832435428884993 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_803 : ((3373981566876187685 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((803 / 8 : ℚ) : ℝ) ∧
    heightZ ((803 / 8 : ℚ) : ℝ) ≤ ((421747695859523461 / 2305843009213693952 : ℚ) : ℝ) := by
  have h : ((3373981566876187685 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((803 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-5 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((803 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-5 / 16 : ℚ) : ℝ) ≤ ((421747695859523461 / 2305843009213693952 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_803 : ((27209528765130543 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((803 / 8 : ℚ) : ℝ) ∧
    logKernel ((803 / 8 : ℚ) : ℝ) ≤ ((6802382191282637 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_803
  constructor
  · exact (show ((27209528765130543 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((3373981566876187685 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((803 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((421747695859523461 / 2305843009213693952 : ℚ) : ℝ) ≤ ((6802382191282637 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_804 : ((2977528282145755563 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((201 / 2 : ℚ) : ℝ) ∧
    heightZ ((201 / 2 : ℚ) : ℝ) ≤ ((1488764141072877783 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((2977528282145755563 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((201 / 2 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-7 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((201 / 2 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-7 / 16 : ℚ) : ℝ) ≤ ((1488764141072877783 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_804 : ((24012324856014155 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((201 / 2 : ℚ) : ℝ) ∧
    logKernel ((201 / 2 : ℚ) : ℝ) ≤ ((1500770303500885 / 4503599627370496 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_804
  constructor
  · exact (show ((24012324856014155 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((2977528282145755563 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((201 / 2 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1488764141072877783 / 9223372036854775808 : ℚ) : ℝ) ≤ ((1500770303500885 / 4503599627370496 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_805 : ((1313829743175830271 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((805 / 8 : ℚ) : ℝ) ∧
    heightZ ((805 / 8 : ℚ) : ℝ) ≤ ((2627659486351660545 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((1313829743175830271 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((805 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-9 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((805 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-9 / 16 : ℚ) : ℝ) ≤ ((2627659486351660545 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_805 : ((21190802309287583 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((805 / 8 : ℚ) : ℝ) ∧
    logKernel ((805 / 8 : ℚ) : ℝ) ≤ ((5297700577321897 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_805
  constructor
  · exact (show ((21190802309287583 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((1313829743175830271 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((805 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((2627659486351660545 / 18446744073709551616 : ℚ) : ℝ) ≤ ((5297700577321897 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_806 : ((2318901357752369367 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((403 / 4 : ℚ) : ℝ) ∧
    heightZ ((403 / 4 : ℚ) : ℝ) ≤ ((1159450678876184685 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((2318901357752369367 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((403 / 4 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-11 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((403 / 4 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-11 / 16 : ℚ) : ℝ) ≤ ((1159450678876184685 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_806 : ((18700817401228783 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((403 / 4 : ℚ) : ℝ) ∧
    logKernel ((403 / 4 : ℚ) : ℝ) ≤ ((4675204350307197 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_806
  constructor
  · exact (show ((18700817401228783 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((2318901357752369367 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((403 / 4 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1159450678876184685 / 9223372036854775808 : ℚ) : ℝ) ≤ ((4675204350307197 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_807 : ((2046423265615678723 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((807 / 8 : ℚ) : ℝ) ∧
    heightZ ((807 / 8 : ℚ) : ℝ) ≤ ((1023211632807839363 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((2046423265615678723 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((807 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-13 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((807 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-13 / 16 : ℚ) : ℝ) ≤ ((1023211632807839363 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_807 : ((16503413432384503 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((807 / 8 : ℚ) : ℝ) ∧
    logKernel ((807 / 8 : ℚ) : ℝ) ≤ ((4125853358096127 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_807
  constructor
  · exact (show ((16503413432384503 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((2046423265615678723 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((807 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1023211632807839363 / 9223372036854775808 : ℚ) : ℝ) ≤ ((4125853358096127 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_808 : ((1805962193282889229 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((101 / 1 : ℚ) : ℝ) ∧
    heightZ ((101 / 1 : ℚ) : ℝ) ≤ ((112872637080180577 / 1152921504606846976 : ℚ) : ℝ) := by
  have h : ((1805962193282889229 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((101 / 1 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-15 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((101 / 1 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-15 / 16 : ℚ) : ℝ) ≤ ((112872637080180577 / 1152921504606846976 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_808 : ((7282105618076165 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((101 / 1 : ℚ) : ℝ) ∧
    logKernel ((101 / 1 : ℚ) : ℝ) ≤ ((14564211236152335 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_808
  constructor
  · exact (show ((7282105618076165 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((1805962193282889229 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((101 / 1 : ℚ) : ℝ)) hh).trans
      (show zKernel ((112872637080180577 / 1152921504606846976 : ℚ) : ℝ) ≤ ((14564211236152335 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_809 : ((796878020878516075 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((809 / 8 : ℚ) : ℝ) ∧
    heightZ ((809 / 8 : ℚ) : ℝ) ≤ ((1593756041757032153 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((796878020878516075 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((809 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-17 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((809 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-17 / 16 : ℚ) : ℝ) ≤ ((1593756041757032153 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_809 : ((401652228265381 / 2251799813685248 : ℚ) : ℝ) ≤ logKernel ((809 / 8 : ℚ) : ℝ) ∧
    logKernel ((809 / 8 : ℚ) : ℝ) ≤ ((12852871304492197 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_809
  constructor
  · exact (show ((401652228265381 / 2251799813685248 : ℚ) : ℝ) ≤ zKernel ((796878020878516075 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((809 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1593756041757032153 / 18446744073709551616 : ℚ) : ℝ) ≤ ((12852871304492197 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_810 : ((351621192581516491 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((405 / 4 : ℚ) : ℝ) ∧
    heightZ ((405 / 4 : ℚ) : ℝ) ≤ ((1406484770326065967 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((351621192581516491 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((405 / 4 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-19 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((405 / 4 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-19 / 16 : ℚ) : ℝ) ≤ ((1406484770326065967 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_810 : ((2835654778883197 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((405 / 4 : ℚ) : ℝ) ∧
    logKernel ((405 / 4 : ℚ) : ℝ) ≤ ((11342619115532793 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_810
  constructor
  · exact (show ((2835654778883197 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((351621192581516491 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((405 / 4 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1406484770326065967 / 18446744073709551616 : ℚ) : ℝ) ≤ ((11342619115532793 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_811 : ((620609226672579637 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((811 / 8 : ℚ) : ℝ) ∧
    heightZ ((811 / 8 : ℚ) : ℝ) ≤ ((1241218453345159277 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((620609226672579637 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((811 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-21 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((811 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-21 / 16 : ℚ) : ℝ) ≤ ((1241218453345159277 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_811 : ((2502456559163627 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((811 / 8 : ℚ) : ℝ) ∧
    logKernel ((811 / 8 : ℚ) : ℝ) ≤ ((10009826236654513 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_811
  constructor
  · exact (show ((2502456559163627 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((620609226672579637 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((811 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1241218453345159277 / 18446744073709551616 : ℚ) : ℝ) ≤ ((10009826236654513 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_812 : ((1095371440507945197 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((203 / 2 : ℚ) : ℝ) ∧
    heightZ ((203 / 2 : ℚ) : ℝ) ≤ ((68460715031746575 / 1152921504606846976 : ℚ) : ℝ) := by
  have h : ((1095371440507945197 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((203 / 2 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-23 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((203 / 2 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-23 / 16 : ℚ) : ℝ) ≤ ((68460715031746575 / 1152921504606846976 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_812 : ((2208410162314405 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((203 / 2 : ℚ) : ℝ) ∧
    logKernel ((203 / 2 : ℚ) : ℝ) ≤ ((8833640649257625 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_812
  constructor
  · exact (show ((2208410162314405 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((1095371440507945197 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((203 / 2 : ℚ) : ℝ)) hh).trans
      (show zKernel ((68460715031746575 / 1152921504606846976 : ℚ) : ℝ) ≤ ((8833640649257625 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_813 : ((966661903427888051 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((813 / 8 : ℚ) : ℝ) ∧
    heightZ ((813 / 8 : ℚ) : ℝ) ≤ ((483330951713944027 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((966661903427888051 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((813 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-25 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((813 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-25 / 16 : ℚ) : ℝ) ≤ ((483330951713944027 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_813 : ((974457563939403 / 9007199254740992 : ℚ) : ℝ) ≤ logKernel ((813 / 8 : ℚ) : ℝ) ∧
    logKernel ((813 / 8 : ℚ) : ℝ) ≤ ((7795660511515229 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_813
  constructor
  · exact (show ((974457563939403 / 9007199254740992 : ℚ) : ℝ) ≤ zKernel ((966661903427888051 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((813 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((483330951713944027 / 9223372036854775808 : ℚ) : ℝ) ≤ ((7795660511515229 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_814 : ((426538067810820245 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((407 / 4 : ℚ) : ℝ) ∧
    heightZ ((407 / 4 : ℚ) : ℝ) ≤ ((853076135621640493 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((426538067810820245 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((407 / 4 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-27 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((407 / 4 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-27 / 16 : ℚ) : ℝ) ≤ ((853076135621640493 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_814 : ((6879646255013227 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((407 / 4 : ℚ) : ℝ) ∧
    logKernel ((407 / 4 : ℚ) : ℝ) ≤ ((429977890938327 / 4503599627370496 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_814
  constructor
  · exact (show ((6879646255013227 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((426538067810820245 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((407 / 4 : ℚ) : ℝ)) hh).trans
      (show zKernel ((853076135621640493 / 18446744073709551616 : ℚ) : ℝ) ≤ ((429977890938327 / 4503599627370496 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_815 : ((188209261838733491 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((815 / 8 : ℚ) : ℝ) ∧
    heightZ ((815 / 8 : ℚ) : ℝ) ≤ ((752837047354933967 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((188209261838733491 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((815 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-29 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((815 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-29 / 16 : ℚ) : ℝ) ≤ ((752837047354933967 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_815 : ((1517816627731721 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((815 / 8 : ℚ) : ℝ) ∧
    logKernel ((815 / 8 : ℚ) : ℝ) ≤ ((6071266510926889 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_815
  constructor
  · exact (show ((1517816627731721 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((188209261838733491 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((815 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((752837047354933967 / 18446744073709551616 : ℚ) : ℝ) ≤ ((6071266510926889 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_816 : ((332188181220830797 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((102 / 1 : ℚ) : ℝ) ∧
    heightZ ((102 / 1 : ℚ) : ℝ) ≤ ((664376362441661597 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((332188181220830797 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((102 / 1 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-31 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((102 / 1 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-31 / 16 : ℚ) : ℝ) ≤ ((664376362441661597 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_816 : ((5357873890658559 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((102 / 1 : ℚ) : ℝ) ∧
    logKernel ((102 / 1 : ℚ) : ℝ) ≤ ((1339468472664641 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_816
  constructor
  · exact (show ((5357873890658559 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((332188181220830797 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((102 / 1 : ℚ) : ℝ)) hh).trans
      (show zKernel ((664376362441661597 / 18446744073709551616 : ℚ) : ℝ) ≤ ((1339468472664641 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_817 : ((9161095031331045 / 288230376151711744 : ℚ) : ℝ) ≤ heightZ ((817 / 8 : ℚ) : ℝ) ∧
    heightZ ((817 / 8 : ℚ) : ℝ) ≤ ((586310082005186883 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((9161095031331045 / 288230376151711744 : ℚ) : ℝ) ≤ Real.exp (-((817 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-33 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((817 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-33 / 16 : ℚ) : ℝ) ≤ ((586310082005186883 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_817 : ((4728307112945053 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((817 / 8 : ℚ) : ℝ) ∧
    logKernel ((817 / 8 : ℚ) : ℝ) ≤ ((2364153556472529 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_817
  constructor
  · exact (show ((4728307112945053 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((9161095031331045 / 288230376151711744 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((817 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((586310082005186883 / 18446744073709551616 : ℚ) : ℝ) ≤ ((2364153556472529 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_818 : ((129354207830924387 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((409 / 4 : ℚ) : ℝ) ∧
    heightZ ((409 / 4 : ℚ) : ℝ) ≤ ((517416831323697551 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((129354207830924387 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((409 / 4 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-35 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((409 / 4 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-35 / 16 : ℚ) : ℝ) ≤ ((517416831323697551 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_818 : ((130397386926335 / 2251799813685248 : ℚ) : ℝ) ≤ logKernel ((409 / 4 : ℚ) : ℝ) ∧
    logKernel ((409 / 4 : ℚ) : ℝ) ≤ ((4172716381642725 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_818
  constructor
  · exact (show ((130397386926335 / 2251799813685248 : ℚ) : ℝ) ≤ zKernel ((129354207830924387 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((409 / 4 : ℚ) : ℝ)) hh).trans
      (show zKernel ((517416831323697551 / 18446744073709551616 : ℚ) : ℝ) ≤ ((4172716381642725 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_819 : ((228309375494149573 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((819 / 8 : ℚ) : ℝ) ∧
    heightZ ((819 / 8 : ℚ) : ℝ) ≤ ((456618750988299149 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((228309375494149573 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((819 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-37 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((819 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-37 / 16 : ℚ) : ℝ) ≤ ((456618750988299149 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_819 : ((920602320540925 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((819 / 8 : ℚ) : ℝ) ∧
    logKernel ((819 / 8 : ℚ) : ℝ) ≤ ((3682409282163705 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_819
  constructor
  · exact (show ((920602320540925 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((228309375494149573 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((819 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((456618750988299149 / 18446744073709551616 : ℚ) : ℝ) ≤ ((3682409282163705 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_820 : ((402964633409220657 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((205 / 2 : ℚ) : ℝ) ∧
    heightZ ((205 / 2 : ℚ) : ℝ) ≤ ((100741158352305165 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((402964633409220657 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((205 / 2 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-39 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((205 / 2 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-39 / 16 : ℚ) : ℝ) ≤ ((100741158352305165 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_820 : ((3249714785558229 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((205 / 2 : ℚ) : ℝ) ∧
    logKernel ((205 / 2 : ℚ) : ℝ) ≤ ((1624857392779117 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_820
  constructor
  · exact (show ((3249714785558229 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((402964633409220657 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((205 / 2 : ℚ) : ℝ)) hh).trans
      (show zKernel ((100741158352305165 / 4611686018427387904 : ℚ) : ℝ) ≤ ((1624857392779117 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_821 : ((44451880104346775 / 2305843009213693952 : ℚ) : ℝ) ≤ heightZ ((821 / 8 : ℚ) : ℝ) ∧
    heightZ ((821 / 8 : ℚ) : ℝ) ≤ ((355615040834774203 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((44451880104346775 / 2305843009213693952 : ℚ) : ℝ) ≤ Real.exp (-((821 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-41 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((821 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-41 / 16 : ℚ) : ℝ) ≤ ((355615040834774203 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_821 : ((2867863232538499 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((821 / 8 : ℚ) : ℝ) ∧
    logKernel ((821 / 8 : ℚ) : ℝ) ≤ ((358482904067313 / 9007199254740992 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_821
  constructor
  · exact (show ((2867863232538499 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((44451880104346775 / 2305843009213693952 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((821 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((355615040834774203 / 18446744073709551616 : ℚ) : ℝ) ≤ ((358482904067313 / 9007199254740992 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_822 : ((313829172049182643 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((411 / 4 : ℚ) : ℝ) ∧
    heightZ ((411 / 4 : ℚ) : ℝ) ≤ ((156914586024591323 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((313829172049182643 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((411 / 4 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-43 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((411 / 4 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-43 / 16 : ℚ) : ℝ) ≤ ((156914586024591323 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_822 : ((1265440209875735 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((411 / 4 : ℚ) : ℝ) ∧
    logKernel ((411 / 4 : ℚ) : ℝ) ≤ ((2530880419751475 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_822
  constructor
  · exact (show ((1265440209875735 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((313829172049182643 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((411 / 4 : ℚ) : ℝ)) hh).trans
      (show zKernel ((156914586024591323 / 9223372036854775808 : ℚ) : ℝ) ≤ ((2530880419751475 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_823 : ((276953272274091765 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((823 / 8 : ℚ) : ℝ) ∧
    heightZ ((823 / 8 : ℚ) : ℝ) ≤ ((34619159034261471 / 2305843009213693952 : ℚ) : ℝ) := by
  have h : ((276953272274091765 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((823 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-45 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((823 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-45 / 16 : ℚ) : ℝ) ≤ ((34619159034261471 / 2305843009213693952 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_823 : ((2146107972766369 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((823 / 8 : ℚ) : ℝ) ∧
    logKernel ((823 / 8 : ℚ) : ℝ) ≤ ((1073053986383187 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_823
  constructor
  · exact (show ((2146107972766369 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((276953272274091765 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((823 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((34619159034261471 / 2305843009213693952 : ℚ) : ℝ) ≤ ((1073053986383187 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_824 : ((30551300617819261 / 2305843009213693952 : ℚ) : ℝ) ≤ heightZ ((103 / 1 : ℚ) : ℝ) ∧
    heightZ ((103 / 1 : ℚ) : ℝ) ≤ ((244410404942554091 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((30551300617819261 / 2305843009213693952 : ℚ) : ℝ) ≤ Real.exp (-((103 / 1 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-47 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((103 / 1 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-47 / 16 : ℚ) : ℝ) ≤ ((244410404942554091 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_824 : ((1671390569746233 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((103 / 1 : ℚ) : ℝ) ∧
    logKernel ((103 / 1 : ℚ) : ℝ) ≤ ((835695284873119 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_824
  constructor
  · exact (show ((1671390569746233 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((30551300617819261 / 2305843009213693952 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((103 / 1 : ℚ) : ℝ)) hh).trans
      (show zKernel ((244410404942554091 / 18446744073709551616 : ℚ) : ℝ) ≤ ((835695284873119 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_825 : ((215691425321250669 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((825 / 8 : ℚ) : ℝ) ∧
    heightZ ((825 / 8 : ℚ) : ℝ) ≤ ((13480714082578167 / 1152921504606846976 : ℚ) : ℝ) := by
  have h : ((215691425321250669 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((825 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-49 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((825 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-49 / 16 : ℚ) : ℝ) ≤ ((13480714082578167 / 1152921504606846976 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_825 : ((1301680284536527 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((825 / 8 : ℚ) : ℝ) ∧
    logKernel ((825 / 8 : ℚ) : ℝ) ≤ ((325420071134133 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_825
  constructor
  · exact (show ((1301680284536527 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((215691425321250669 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((825 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((13480714082578167 / 1152921504606846976 : ℚ) : ℝ) ≤ ((325420071134133 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_826 : ((95173507380030143 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((413 / 4 : ℚ) : ℝ) ∧
    heightZ ((413 / 4 : ℚ) : ℝ) ≤ ((190347014760060289 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((95173507380030143 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((413 / 4 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-51 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((413 / 4 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-51 / 16 : ℚ) : ℝ) ≤ ((190347014760060289 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_826 : ((126718703113207 / 9007199254740992 : ℚ) : ℝ) ≤ logKernel ((413 / 4 : ℚ) : ℝ) ∧
    logKernel ((413 / 4 : ℚ) : ℝ) ≤ ((1013749624905661 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_826
  constructor
  · exact (show ((126718703113207 / 9007199254740992 : ℚ) : ℝ) ≤ zKernel ((95173507380030143 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((413 / 4 : ℚ) : ℝ)) hh).trans
      (show zKernel ((190347014760060289 / 18446744073709551616 : ℚ) : ℝ) ≤ ((1013749624905661 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_827 : ((167980650941977465 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((827 / 8 : ℚ) : ℝ) ∧
    heightZ ((827 / 8 : ℚ) : ℝ) ≤ ((41995162735494367 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((167980650941977465 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((827 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-53 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((827 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-53 / 16 : ℚ) : ℝ) ≤ ((41995162735494367 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_827 : ((789509001714867 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((827 / 8 : ℚ) : ℝ) ∧
    logKernel ((827 / 8 : ℚ) : ℝ) ≤ ((98688625214359 / 9007199254740992 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_827
  constructor
  · exact (show ((789509001714867 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((167980650941977465 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((827 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((41995162735494367 / 4611686018427387904 : ℚ) : ℝ) ≤ ((98688625214359 / 9007199254740992 : ℚ) : ℝ) by norm_num [zKernel])

theorem log_height_bounds_0 : ((165738146016839943 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((199 / 2 : ℚ) : ℝ) ∧
    Real.log ((199 / 2 : ℚ) : ℝ) ≤ ((331476292033679889 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((165738146016839943 / 36028797018963968 : ℚ) : ℝ) ≤ ((199 / 2 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((199 / 2 : ℚ) : ℝ) ≤ Real.exp ((331476292033679889 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_0 : heightPower (0 : Fin 125) ≤ ((7047967639653 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_0
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_0 : heightFactor (0 : Fin 125) ≤ ((271316576601750073 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_0
  obtain ⟨hpl, hph⟩ := kernel_bounds_795
  obtain ⟨hcl, hch⟩ := kernel_bounds_796
  obtain ⟨hzl, hzh⟩ := height_z_bounds_796
  have h : (((39601 / 2 : ℚ) : ℝ) * (logKernel ((795 / 8 : ℚ) : ℝ) - logKernel ((199 / 2 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((199 / 2 : ℚ) : ℝ) + Real.log ((199 / 2 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((271316576601750073 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_1 : ((331566759834688133 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((797 / 8 : ℚ) : ℝ) ∧
    Real.log ((797 / 8 : ℚ) : ℝ) ≤ ((41445844979336017 / 9007199254740992 : ℚ) : ℝ) := by
  have hl : Real.exp ((331566759834688133 / 72057594037927936 : ℚ) : ℝ) ≤ ((797 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((797 / 8 : ℚ) : ℝ) ≤ Real.exp ((41445844979336017 / 9007199254740992 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_1 : heightPower (1 : Fin 125) ≤ ((15932408123783 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_1
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_1 : heightFactor (1 : Fin 125) ≤ ((320664859037327275 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_1
  obtain ⟨hpl, hph⟩ := kernel_bounds_796
  obtain ⟨hcl, hch⟩ := kernel_bounds_797
  obtain ⟨hzl, hzh⟩ := height_z_bounds_797
  have h : (((635209 / 32 : ℚ) : ℝ) * (logKernel ((199 / 2 : ℚ) : ℝ) - logKernel ((797 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((797 / 8 : ℚ) : ℝ) + Real.log ((797 / 8 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((320664859037327275 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_2 : ((41457139274552215 / 9007199254740992 : ℚ) : ℝ) ≤ Real.log ((399 / 4 : ℚ) : ℝ) ∧
    Real.log ((399 / 4 : ℚ) : ℝ) ≤ ((331657114196417723 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((41457139274552215 / 9007199254740992 : ℚ) : ℝ) ≤ ((399 / 4 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((399 / 4 : ℚ) : ℝ) ≤ Real.exp ((331657114196417723 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_2 : heightPower (2 : Fin 125) ≤ ((49633475654735 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_2
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_2 : heightFactor (2 : Fin 125) ≤ ((591780732696578779 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_2
  obtain ⟨hpl, hph⟩ := kernel_bounds_797
  obtain ⟨hcl, hch⟩ := kernel_bounds_798
  obtain ⟨hzl, hzh⟩ := height_z_bounds_798
  have h : (((159201 / 8 : ℚ) : ℝ) * (logKernel ((797 / 8 : ℚ) : ℝ) - logKernel ((399 / 4 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((399 / 4 : ℚ) : ℝ) + Real.log ((399 / 4 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((591780732696578779 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_3 : ((331747355402999703 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((799 / 8 : ℚ) : ℝ) ∧
    Real.log ((799 / 8 : ℚ) : ℝ) ≤ ((165873677701499853 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((331747355402999703 / 72057594037927936 : ℚ) : ℝ) ≤ ((799 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((799 / 8 : ℚ) : ℝ) ≤ Real.exp ((165873677701499853 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_3 : heightPower (3 : Fin 125) ≤ ((134803828111513 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_3
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_3 : heightFactor (3 : Fin 125) ≤ ((273028944805986455 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_3
  obtain ⟨hpl, hph⟩ := kernel_bounds_798
  obtain ⟨hcl, hch⟩ := kernel_bounds_799
  obtain ⟨hzl, hzh⟩ := height_z_bounds_799
  have h : (((638401 / 32 : ℚ) : ℝ) * (logKernel ((399 / 4 : ℚ) : ℝ) - logKernel ((799 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((799 / 8 : ℚ) : ℝ) + Real.log ((799 / 8 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((273028944805986455 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_4 : ((331837483737498975 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((100 / 1 : ℚ) : ℝ) ∧
    Real.log ((100 / 1 : ℚ) : ℝ) ≤ ((165918741868749489 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((331837483737498975 / 72057594037927936 : ℚ) : ℝ) ≤ ((100 / 1 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((100 / 1 : ℚ) : ℝ) ≤ Real.exp ((165918741868749489 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_4 : heightPower (4 : Fin 125) ≤ ((170340264006983 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_4
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_4 : heightFactor (4 : Fin 125) ≤ ((503865895760563863 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_4
  obtain ⟨hpl, hph⟩ := kernel_bounds_799
  obtain ⟨hcl, hch⟩ := kernel_bounds_800
  obtain ⟨hzl, hzh⟩ := height_z_bounds_800
  have h : (((20000 / 1 : ℚ) : ℝ) * (logKernel ((799 / 8 : ℚ) : ℝ) - logKernel ((100 / 1 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((100 / 1 : ℚ) : ℝ) + Real.log ((100 / 1 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((503865895760563863 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_5 : ((331927499481919603 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((801 / 8 : ℚ) : ℝ) ∧
    Real.log ((801 / 8 : ℚ) : ℝ) ≤ ((165963749740959803 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((331927499481919603 / 72057594037927936 : ℚ) : ℝ) ≤ ((801 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((801 / 8 : ℚ) : ℝ) ≤ Real.exp ((165963749740959803 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_5 : heightPower (5 : Fin 125) ≤ ((102938130048729 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_5
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_5 : heightFactor (5 : Fin 125) ≤ ((464932235453528231 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_5
  obtain ⟨hpl, hph⟩ := kernel_bounds_800
  obtain ⟨hcl, hch⟩ := kernel_bounds_801
  obtain ⟨hzl, hzh⟩ := height_z_bounds_801
  have h : (((641601 / 32 : ℚ) : ℝ) * (logKernel ((100 / 1 : ℚ) : ℝ) - logKernel ((801 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((801 / 8 : ℚ) : ℝ) + Real.log ((801 / 8 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((464932235453528231 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_6 : ((162117872518169 / 35184372088832 : ℚ) : ℝ) ≤ Real.log ((401 / 4 : ℚ) : ℝ) ∧
    Real.log ((401 / 4 : ℚ) : ℝ) ≤ ((332017402917210115 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((162117872518169 / 35184372088832 : ℚ) : ℝ) ≤ ((401 / 4 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((401 / 4 : ℚ) : ℝ) ≤ Real.exp ((332017402917210115 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_6 : heightPower (6 : Fin 125) ≤ ((120705908740197 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_6
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_6 : heightFactor (6 : Fin 125) ≤ ((429005414455213921 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_6
  obtain ⟨hpl, hph⟩ := kernel_bounds_801
  obtain ⟨hcl, hch⟩ := kernel_bounds_802
  obtain ⟨hzl, hzh⟩ := height_z_bounds_802
  have h : (((160801 / 8 : ℚ) : ℝ) * (logKernel ((801 / 8 : ℚ) : ℝ) - logKernel ((401 / 4 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((401 / 4 : ℚ) : ℝ) + Real.log ((401 / 4 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((429005414455213921 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_7 : ((332107194323268757 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((803 / 8 : ℚ) : ℝ) ∧
    Real.log ((803 / 8 : ℚ) : ℝ) ≤ ((41513399290408595 / 9007199254740992 : ℚ) : ℝ) := by
  have hl : Real.exp ((332107194323268757 / 72057594037927936 : ℚ) : ℝ) ≤ ((803 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((803 / 8 : ℚ) : ℝ) ≤ Real.exp ((41513399290408595 / 9007199254740992 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_7 : heightPower (7 : Fin 125) ≤ ((138473468624571 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_7
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_7 : heightFactor (7 : Fin 125) ≤ ((395853339349042425 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_7
  obtain ⟨hpl, hph⟩ := kernel_bounds_802
  obtain ⟨hcl, hch⟩ := kernel_bounds_803
  obtain ⟨hzl, hzh⟩ := height_z_bounds_803
  have h : (((644809 / 32 : ℚ) : ℝ) * (logKernel ((401 / 4 : ℚ) : ℝ) - logKernel ((803 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((803 / 8 : ℚ) : ℝ) + Real.log ((803 / 8 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((395853339349042425 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_8 : ((166098436989474371 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((201 / 2 : ℚ) : ℝ) ∧
    Real.log ((201 / 2 : ℚ) : ℝ) ≤ ((332196873978948745 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((166098436989474371 / 36028797018963968 : ℚ) : ℝ) ≤ ((201 / 2 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((201 / 2 : ℚ) : ℝ) ≤ Real.exp ((332196873978948745 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_8 : heightPower (8 : Fin 125) ≤ ((156240810246487 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_8
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_8 : heightFactor (8 : Fin 125) ≤ ((365261821771063157 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_8
  obtain ⟨hpl, hph⟩ := kernel_bounds_803
  obtain ⟨hcl, hch⟩ := kernel_bounds_804
  obtain ⟨hzl, hzh⟩ := height_z_bounds_804
  have h : (((40401 / 2 : ℚ) : ℝ) * (logKernel ((803 / 8 : ℚ) : ℝ) - logKernel ((201 / 2 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((201 / 2 : ℚ) : ℝ) + Real.log ((201 / 2 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((365261821771063157 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_9 : ((332286442162063423 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((805 / 8 : ℚ) : ℝ) ∧
    Real.log ((805 / 8 : ℚ) : ℝ) ≤ ((166143221081031713 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((332286442162063423 / 72057594037927936 : ℚ) : ℝ) ≤ ((805 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((805 / 8 : ℚ) : ℝ) ≤ Real.exp ((166143221081031713 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_9 : heightPower (9 : Fin 125) ≤ ((174007934148549 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_9
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_9 : heightFactor (9 : Fin 125) ≤ ((337033197896167353 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_9
  obtain ⟨hpl, hph⟩ := kernel_bounds_804
  obtain ⟨hcl, hch⟩ := kernel_bounds_805
  obtain ⟨hzl, hzh⟩ := height_z_bounds_805
  have h : (((648025 / 32 : ℚ) : ℝ) * (logKernel ((201 / 2 : ℚ) : ℝ) - logKernel ((805 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((805 / 8 : ℚ) : ℝ) + Real.log ((805 / 8 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((337033197896167353 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_10 : ((332375899149391465 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((403 / 4 : ℚ) : ℝ) ∧
    Real.log ((403 / 4 : ℚ) : ℝ) ≤ ((83093974787347867 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((332375899149391465 / 72057594037927936 : ℚ) : ℝ) ≤ ((403 / 4 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((403 / 4 : ℚ) : ℝ) ≤ Real.exp ((83093974787347867 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_10 : heightPower (10 : Fin 125) ≤ ((47943710217835 / 35184372088832 : ℚ) : ℝ) := by
  have hh := log_height_bounds_10
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_10 : heightFactor (10 : Fin 125) ≤ ((155492527150934343 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_10
  obtain ⟨hpl, hph⟩ := kernel_bounds_805
  obtain ⟨hcl, hch⟩ := kernel_bounds_806
  obtain ⟨hzl, hzh⟩ := height_z_bounds_806
  have h : (((162409 / 8 : ℚ) : ℝ) * (logKernel ((805 / 8 : ℚ) : ℝ) - logKernel ((403 / 4 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((403 / 4 : ℚ) : ℝ) + Real.log ((403 / 4 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((155492527150934343 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_11 : ((166232622608340991 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((807 / 8 : ℚ) : ℝ) ∧
    Real.log ((807 / 8 : ℚ) : ℝ) ≤ ((332465245216681985 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((166232622608340991 / 36028797018963968 : ℚ) : ℝ) ≤ ((807 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((807 / 8 : ℚ) : ℝ) ≤ Real.exp ((332465245216681985 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_11 : heightPower (11 : Fin 125) ≤ ((419083061906865 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_11
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_11 : heightFactor (11 : Fin 125) ≤ ((286949052017557445 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_11
  obtain ⟨hpl, hph⟩ := kernel_bounds_806
  obtain ⟨hcl, hch⟩ := kernel_bounds_807
  obtain ⟨hzl, hzh⟩ := height_z_bounds_807
  have h : (((651249 / 32 : ℚ) : ℝ) * (logKernel ((403 / 4 : ℚ) : ℝ) - logKernel ((807 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((807 / 8 : ℚ) : ℝ) + Real.log ((807 / 8 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((286949052017557445 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_12 : ((166277240319329815 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((101 / 1 : ℚ) : ℝ) ∧
    Real.log ((101 / 1 : ℚ) : ℝ) ≤ ((332554480638659633 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((166277240319329815 / 36028797018963968 : ℚ) : ℝ) ≤ ((101 / 1 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((101 / 1 : ℚ) : ℝ) ≤ Real.exp ((332554480638659633 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_12 : heightPower (12 : Fin 125) ≤ ((227308004931399 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_12
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_12 : heightFactor (12 : Fin 125) ≤ ((264769841197607621 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_12
  obtain ⟨hpl, hph⟩ := kernel_bounds_807
  obtain ⟨hcl, hch⟩ := kernel_bounds_808
  obtain ⟨hzl, hzh⟩ := height_z_bounds_808
  have h : (((20402 / 1 : ℚ) : ℝ) * (logKernel ((807 / 8 : ℚ) : ℝ) - logKernel ((101 / 1 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((101 / 1 : ℚ) : ℝ) + Real.log ((101 / 1 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((264769841197607621 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_13 : ((332643605689029679 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((809 / 8 : ℚ) : ℝ) ∧
    Real.log ((809 / 8 : ℚ) : ℝ) ≤ ((166321802844514841 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((332643605689029679 / 72057594037927936 : ℚ) : ℝ) ≤ ((809 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((809 / 8 : ℚ) : ℝ) ≤ Real.exp ((166321802844514841 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_13 : heightPower (13 : Fin 125) ≤ ((245074263339819 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_13
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_13 : heightFactor (13 : Fin 125) ≤ ((61076014859674633 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_13
  obtain ⟨hpl, hph⟩ := kernel_bounds_808
  obtain ⟨hcl, hch⟩ := kernel_bounds_809
  obtain ⟨hzl, hzh⟩ := height_z_bounds_809
  have h : (((654481 / 32 : ℚ) : ℝ) * (logKernel ((101 / 1 : ℚ) : ℝ) - logKernel ((809 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((809 / 8 : ℚ) : ℝ) + Real.log ((809 / 8 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((61076014859674633 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_14 : ((41591577580060381 / 9007199254740992 : ℚ) : ℝ) ≤ Real.log ((405 / 4 : ℚ) : ℝ) ∧
    Real.log ((405 / 4 : ℚ) : ℝ) ≤ ((332732620640483051 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((41591577580060381 / 9007199254740992 : ℚ) : ℝ) ≤ ((405 / 4 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((405 / 4 : ℚ) : ℝ) ≤ Real.exp ((332732620640483051 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_14 : heightPower (14 : Fin 125) ≤ ((65710076677823 / 35184372088832 : ℚ) : ℝ) := by
  have hh := log_height_bounds_14
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_14 : heightFactor (14 : Fin 125) ≤ ((28177425912366443 / 35184372088832 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_14
  obtain ⟨hpl, hph⟩ := kernel_bounds_809
  obtain ⟨hcl, hch⟩ := kernel_bounds_810
  obtain ⟨hzl, hzh⟩ := height_z_bounds_810
  have h : (((164025 / 8 : ℚ) : ℝ) * (logKernel ((809 / 8 : ℚ) : ℝ) - logKernel ((405 / 4 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((405 / 4 : ℚ) : ℝ) + Real.log ((405 / 4 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((28177425912366443 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_15 : ((332821525764701313 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((811 / 8 : ℚ) : ℝ) ∧
    Real.log ((811 / 8 : ℚ) : ℝ) ≤ ((83205381441175329 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((332821525764701313 / 72057594037927936 : ℚ) : ℝ) ≤ ((811 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((811 / 8 : ℚ) : ℝ) ≤ Real.exp ((83205381441175329 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_15 : heightPower (15 : Fin 125) ≤ ((280606135576447 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_15
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_15 : heightFactor (15 : Fin 125) ≤ ((51998448768054689 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_15
  obtain ⟨hpl, hph⟩ := kernel_bounds_810
  obtain ⟨hcl, hch⟩ := kernel_bounds_811
  obtain ⟨hzl, hzh⟩ := height_z_bounds_811
  have h : (((657721 / 32 : ℚ) : ℝ) * (logKernel ((405 / 4 : ℚ) : ℝ) - logKernel ((811 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((811 / 8 : ℚ) : ℝ) + Real.log ((811 / 8 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((51998448768054689 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_16 : ((166455160666180841 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((203 / 2 : ℚ) : ℝ) ∧
    Real.log ((203 / 2 : ℚ) : ℝ) ≤ ((332910321332361685 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((166455160666180841 / 36028797018963968 : ℚ) : ℝ) ≤ ((203 / 2 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((203 / 2 : ℚ) : ℝ) ≤ Real.exp ((332910321332361685 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_16 : heightPower (16 : Fin 125) ≤ ((596743500927899 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_16
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_16 : heightFactor (16 : Fin 125) ≤ ((95957277664585269 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_16
  obtain ⟨hpl, hph⟩ := kernel_bounds_811
  obtain ⟨hcl, hch⟩ := kernel_bounds_812
  obtain ⟨hzl, hzh⟩ := height_z_bounds_812
  have h : (((41209 / 2 : ℚ) : ℝ) * (logKernel ((811 / 8 : ℚ) : ℝ) - logKernel ((203 / 2 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((203 / 2 : ℚ) : ℝ) + Real.log ((203 / 2 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((95957277664585269 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_17 : ((332999007613141937 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((813 / 8 : ℚ) : ℝ) ∧
    Real.log ((813 / 8 : ℚ) : ℝ) ≤ ((83249751903285485 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((332999007613141937 / 72057594037927936 : ℚ) : ℝ) ≤ ((813 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((813 / 8 : ℚ) : ℝ) ≤ Real.exp ((83249751903285485 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_17 : heightPower (17 : Fin 125) ≤ ((632274303801029 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_17
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_17 : heightFactor (17 : Fin 125) ≤ ((22134714519780619 / 35184372088832 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_17
  obtain ⟨hpl, hph⟩ := kernel_bounds_812
  obtain ⟨hcl, hch⟩ := kernel_bounds_813
  obtain ⟨hzl, hzh⟩ := height_z_bounds_813
  have h : (((660969 / 32 : ℚ) : ℝ) * (logKernel ((203 / 2 : ℚ) : ℝ) - logKernel ((813 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((813 / 8 : ℚ) : ℝ) + Real.log ((813 / 8 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((22134714519780619 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_18 : ((333087584875725353 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((407 / 4 : ℚ) : ℝ) ∧
    Real.log ((407 / 4 : ℚ) : ℝ) ≤ ((83271896218931339 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((333087584875725353 / 72057594037927936 : ℚ) : ℝ) ≤ ((407 / 4 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((407 / 4 : ℚ) : ℝ) ≤ Real.exp ((83271896218931339 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_18 : heightPower (18 : Fin 125) ≤ ((166951170205457 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_18
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_18 : heightFactor (18 : Fin 125) ≤ ((20423416303868939 / 35184372088832 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_18
  obtain ⟨hpl, hph⟩ := kernel_bounds_813
  obtain ⟨hcl, hch⟩ := kernel_bounds_814
  obtain ⟨hzl, hzh⟩ := height_z_bounds_814
  have h : (((165649 / 8 : ℚ) : ℝ) * (logKernel ((813 / 8 : ℚ) : ℝ) - logKernel ((407 / 4 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((407 / 4 : ℚ) : ℝ) + Real.log ((407 / 4 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((20423416303868939 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_19 : ((333176053387805577 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((815 / 8 : ℚ) : ℝ) ∧
    Real.log ((815 / 8 : ℚ) : ℝ) ≤ ((83294013346951395 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((333176053387805577 / 72057594037927936 : ℚ) : ℝ) ≤ ((815 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((815 / 8 : ℚ) : ℝ) ≤ Real.exp ((83294013346951395 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_19 : heightPower (19 : Fin 125) ≤ ((703334633035973 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_19
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_19 : heightFactor (19 : Fin 125) ≤ ((75377428387461777 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_19
  obtain ⟨hpl, hph⟩ := kernel_bounds_814
  obtain ⟨hcl, hch⟩ := kernel_bounds_815
  obtain ⟨hzl, hzh⟩ := height_z_bounds_815
  have h : (((664225 / 32 : ℚ) : ℝ) * (logKernel ((407 / 4 : ℚ) : ℝ) - logKernel ((815 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((815 / 8 : ℚ) : ℝ) + Real.log ((815 / 8 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((75377428387461777 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_20 : ((83316103354022871 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((102 / 1 : ℚ) : ℝ) ∧
    Real.log ((102 / 1 : ℚ) : ℝ) ≤ ((333264413416091487 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((83316103354022871 / 18014398509481984 : ℚ) : ℝ) ≤ ((102 / 1 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((102 / 1 : ℚ) : ℝ) ≤ Real.exp ((333264413416091487 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_20 : heightPower (20 : Fin 125) ≤ ((738864161485297 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_20
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_20 : heightFactor (20 : Fin 125) ≤ ((69549294135497461 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_20
  obtain ⟨hpl, hph⟩ := kernel_bounds_815
  obtain ⟨hcl, hch⟩ := kernel_bounds_816
  obtain ⟨hzl, hzh⟩ := height_z_bounds_816
  have h : (((20808 / 1 : ℚ) : ℝ) * (logKernel ((815 / 8 : ℚ) : ℝ) - logKernel ((102 / 1 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((102 / 1 : ℚ) : ℝ) + Real.log ((102 / 1 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((69549294135497461 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_21 : ((333352665226312003 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((817 / 8 : ℚ) : ℝ) ∧
    Real.log ((817 / 8 : ℚ) : ℝ) ≤ ((166676332613156003 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((333352665226312003 / 72057594037927936 : ℚ) : ℝ) ≤ ((817 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((817 / 8 : ℚ) : ℝ) ≤ Real.exp ((166676332613156003 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_21 : heightPower (21 : Fin 125) ≤ ((774393267207803 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_21
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_21 : heightFactor (21 : Fin 125) ≤ ((128343125197167509 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_21
  obtain ⟨hpl, hph⟩ := kernel_bounds_816
  obtain ⟨hcl, hch⟩ := kernel_bounds_817
  obtain ⟨hzl, hzh⟩ := height_z_bounds_817
  have h : (((667489 / 32 : ℚ) : ℝ) * (logKernel ((102 / 1 : ℚ) : ℝ) - logKernel ((817 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((817 / 8 : ℚ) : ℝ) + Real.log ((817 / 8 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((128343125197167509 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_22 : ((166720404541610455 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((409 / 4 : ℚ) : ℝ) ∧
    Real.log ((409 / 4 : ℚ) : ℝ) ≤ ((333440809083220913 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((166720404541610455 / 36028797018963968 : ℚ) : ℝ) ≤ ((409 / 4 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((409 / 4 : ℚ) : ℝ) ≤ Real.exp ((333440809083220913 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_22 : heightPower (22 : Fin 125) ≤ ((809921951237685 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_22
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_22 : heightFactor (22 : Fin 125) ≤ ((118418888425502773 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_22
  obtain ⟨hpl, hph⟩ := kernel_bounds_817
  obtain ⟨hcl, hch⟩ := kernel_bounds_818
  obtain ⟨hzl, hzh⟩ := height_z_bounds_818
  have h : (((167281 / 8 : ℚ) : ℝ) * (logKernel ((817 / 8 : ℚ) : ℝ) - logKernel ((409 / 4 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((409 / 4 : ℚ) : ℝ) + Real.log ((409 / 4 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((118418888425502773 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_23 : ((166764422625300797 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((819 / 8 : ℚ) : ℝ) ∧
    Real.log ((819 / 8 : ℚ) : ℝ) ≤ ((333528845250601597 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((166764422625300797 / 36028797018963968 : ℚ) : ℝ) ≤ ((819 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((819 / 8 : ℚ) : ℝ) ≤ Real.exp ((333528845250601597 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_23 : heightPower (23 : Fin 125) ≤ ((211362553651337 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_23
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_23 : heightFactor (23 : Fin 125) ≤ ((109261670339327755 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_23
  obtain ⟨hpl, hph⟩ := kernel_bounds_818
  obtain ⟨hcl, hch⟩ := kernel_bounds_819
  obtain ⟨hzl, hzh⟩ := height_z_bounds_819
  have h : (((670761 / 32 : ℚ) : ℝ) * (logKernel ((409 / 4 : ℚ) : ℝ) - logKernel ((819 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((819 / 8 : ℚ) : ℝ) + Real.log ((819 / 8 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((109261670339327755 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_24 : ((333616773991271793 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((205 / 2 : ℚ) : ℝ) ∧
    Real.log ((205 / 2 : ℚ) : ℝ) ≤ ((83404193497817949 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((333616773991271793 / 72057594037927936 : ℚ) : ℝ) ≤ ((205 / 2 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((205 / 2 : ℚ) : ℝ) ≤ Real.exp ((83404193497817949 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_24 : heightPower (24 : Fin 125) ≤ ((880978058337423 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_24
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_24 : heightFactor (24 : Fin 125) ≤ ((100812220379390001 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_24
  obtain ⟨hpl, hph⟩ := kernel_bounds_819
  obtain ⟨hcl, hch⟩ := kernel_bounds_820
  obtain ⟨hzl, hzh⟩ := height_z_bounds_820
  have h : (((42025 / 2 : ℚ) : ℝ) * (logKernel ((819 / 8 : ℚ) : ℝ) - logKernel ((205 / 2 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((205 / 2 : ℚ) : ℝ) + Real.log ((205 / 2 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((100812220379390001 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_25 : ((20856537222943019 / 4503599627370496 : ℚ) : ℝ) ≤ Real.log ((821 / 8 : ℚ) : ℝ) ∧
    Real.log ((821 / 8 : ℚ) : ℝ) ≤ ((333704595567088307 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((20856537222943019 / 4503599627370496 : ℚ) : ℝ) ≤ ((821 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((821 / 8 : ℚ) : ℝ) ≤ Real.exp ((333704595567088307 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_25 : heightPower (25 : Fin 125) ≤ ((229126370864197 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_25
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_25 : heightFactor (25 : Fin 125) ≤ ((46507931275136549 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_25
  obtain ⟨hpl, hph⟩ := kernel_bounds_820
  obtain ⟨hcl, hch⟩ := kernel_bounds_821
  obtain ⟨hzl, hzh⟩ := height_z_bounds_821
  have h : (((674041 / 32 : ℚ) : ℝ) * (logKernel ((205 / 2 : ℚ) : ℝ) - logKernel ((821 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((821 / 8 : ℚ) : ℝ) + Real.log ((821 / 8 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((46507931275136549 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_26 : ((333792310238951657 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((411 / 4 : ℚ) : ℝ) ∧
    Real.log ((411 / 4 : ℚ) : ℝ) ≤ ((83448077559737915 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((333792310238951657 / 72057594037927936 : ℚ) : ℝ) ≤ ((411 / 4 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((411 / 4 : ℚ) : ℝ) ≤ Real.exp ((83448077559737915 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_26 : heightPower (26 : Fin 125) ≤ ((476016245491293 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_26
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_26 : heightFactor (26 : Fin 125) ≤ ((85822142423923137 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_26
  obtain ⟨hpl, hph⟩ := kernel_bounds_821
  obtain ⟨hcl, hch⟩ := kernel_bounds_822
  obtain ⟨hzl, hzh⟩ := height_z_bounds_822
  have h : (((168921 / 8 : ℚ) : ℝ) * (logKernel ((821 / 8 : ℚ) : ℝ) - logKernel ((411 / 4 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((411 / 4 : ℚ) : ℝ) + Real.log ((411 / 4 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((85822142423923137 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_27 : ((83469979566702693 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((823 / 8 : ℚ) : ℝ) ∧
    Real.log ((823 / 8 : ℚ) : ℝ) ≤ ((333879918266810775 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((83469979566702693 / 18014398509481984 : ℚ) : ℝ) ≤ ((823 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((823 / 8 : ℚ) : ℝ) ≤ Real.exp ((333879918266810775 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_27 : heightPower (27 : Fin 125) ≤ ((987559081930243 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_27
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_27 : heightFactor (27 : Fin 125) ≤ ((102452653439087041 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_27
  obtain ⟨hpl, hph⟩ := kernel_bounds_822
  obtain ⟨hcl, hch⟩ := kernel_bounds_823
  obtain ⟨hzl, hzh⟩ := height_z_bounds_823
  have h : (((677329 / 32 : ℚ) : ℝ) * (logKernel ((411 / 4 : ℚ) : ℝ) - logKernel ((823 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((823 / 8 : ℚ) : ℝ) + Real.log ((823 / 8 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((102452653439087041 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_28 : ((41745927488708447 / 9007199254740992 : ℚ) : ℝ) ≤ Real.log ((103 / 1 : ℚ) : ℝ) ∧
    Real.log ((103 / 1 : ℚ) : ℝ) ≤ ((333967419909667579 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((41745927488708447 / 9007199254740992 : ℚ) : ℝ) ≤ ((103 / 1 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((103 / 1 : ℚ) : ℝ) ≤ Real.exp ((333967419909667579 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_28 : heightPower (28 : Fin 125) ≤ ((255771314327871 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_28
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_28 : heightFactor (28 : Fin 125) ≤ ((132154071326937785 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_28
  obtain ⟨hpl, hph⟩ := kernel_bounds_823
  obtain ⟨hcl, hch⟩ := kernel_bounds_824
  obtain ⟨hzl, hzh⟩ := height_z_bounds_824
  have h : (((21218 / 1 : ℚ) : ℝ) * (logKernel ((823 / 8 : ℚ) : ℝ) - logKernel ((103 / 1 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((103 / 1 : ℚ) : ℝ) + Real.log ((103 / 1 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((132154071326937785 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_29 : ((334054815425581599 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((825 / 8 : ℚ) : ℝ) ∧
    Real.log ((825 / 8 : ℚ) : ℝ) ≤ ((167027407712790801 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((334054815425581599 / 72057594037927936 : ℚ) : ℝ) ≤ ((825 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((825 / 8 : ℚ) : ℝ) ≤ Real.exp ((167027407712790801 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_29 : heightPower (29 : Fin 125) ≤ ((264652754533589 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_29
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_29 : heightFactor (29 : Fin 125) ≤ ((53802392335737769 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_29
  obtain ⟨hpl, hph⟩ := kernel_bounds_824
  obtain ⟨hcl, hch⟩ := kernel_bounds_825
  obtain ⟨hzl, hzh⟩ := height_z_bounds_825
  have h : (((680625 / 32 : ℚ) : ℝ) * (logKernel ((103 / 1 : ℚ) : ℝ) - logKernel ((825 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((825 / 8 : ℚ) : ℝ) + Real.log ((825 / 8 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((53802392335737769 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_30 : ((167071052535837271 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((413 / 4 : ℚ) : ℝ) ∧
    Real.log ((413 / 4 : ℚ) : ℝ) ≤ ((334142105071674545 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((167071052535837271 / 36028797018963968 : ℚ) : ℝ) ≤ ((413 / 4 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((413 / 4 : ℚ) : ℝ) ≤ Real.exp ((334142105071674545 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_30 : heightPower (30 : Fin 125) ≤ ((547068182701619 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_30
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_30 : heightFactor (30 : Fin 125) ≤ ((43807768740383475 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_30
  obtain ⟨hpl, hph⟩ := kernel_bounds_825
  obtain ⟨hcl, hch⟩ := kernel_bounds_826
  obtain ⟨hzl, hzh⟩ := height_z_bounds_826
  have h : (((170569 / 8 : ℚ) : ℝ) * (logKernel ((825 / 8 : ℚ) : ℝ) - logKernel ((413 / 4 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((413 / 4 : ℚ) : ℝ) + Real.log ((413 / 4 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((43807768740383475 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_31 : ((334229289104134813 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((827 / 8 : ℚ) : ℝ) ∧
    Real.log ((827 / 8 : ℚ) : ℝ) ≤ ((10444665284504213 / 2251799813685248 : ℚ) : ℝ) := by
  have hl : Real.exp ((334229289104134813 / 72057594037927936 : ℚ) : ℝ) ≤ ((827 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((827 / 8 : ℚ) : ℝ) ≤ Real.exp ((10444665284504213 / 2251799813685248 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_31 : heightPower (31 : Fin 125) ≤ ((282415325029717 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_31
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_31 : heightFactor (31 : Fin 125) ≤ ((35669678530138219 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_31
  obtain ⟨hpl, hph⟩ := kernel_bounds_826
  obtain ⟨hcl, hch⟩ := kernel_bounds_827
  obtain ⟨hzl, hzh⟩ := height_z_bounds_827
  have h : (((683929 / 32 : ℚ) : ℝ) * (logKernel ((413 / 4 : ℚ) : ℝ) - logKernel ((827 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((827 / 8 : ℚ) : ℝ) + Real.log ((827 / 8 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((35669678530138219 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

end LegendreK6.M3Far.Enclosures.Height000
