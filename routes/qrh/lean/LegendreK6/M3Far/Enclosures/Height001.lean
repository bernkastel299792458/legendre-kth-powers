import LegendreK6.M3FarDefinitions
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp

/-! Generated proposals: every bound is checked by Lean, not by trusting Arb. -/
namespace LegendreK6.M3Far.Enclosures.Height001
set_option maxRecDepth 100000
set_option maxHeartbeats 0

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

theorem height_z_bounds_828 : ((148242404150439211 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((207 / 2 : ℚ) : ℝ) ∧
    heightZ ((207 / 2 : ℚ) : ℝ) ≤ ((74121202075219607 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((148242404150439211 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((207 / 2 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-55 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((207 / 2 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-55 / 16 : ℚ) : ℝ) ≤ ((74121202075219607 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_828 : ((614870228777461 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((207 / 2 : ℚ) : ℝ) ∧
    logKernel ((207 / 2 : ℚ) : ℝ) ≤ ((307435114388733 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_828
  constructor
  · exact (show ((614870228777461 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((148242404150439211 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((207 / 2 : ℚ) : ℝ)) hh).trans
      (show zKernel ((74121202075219607 / 9223372036854775808 : ℚ) : ℝ) ≤ ((307435114388733 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_829 : ((130823462494456373 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((829 / 8 : ℚ) : ℝ) ∧
    heightZ ((829 / 8 : ℚ) : ℝ) ≤ ((16352932811807047 / 2305843009213693952 : ℚ) : ℝ) := by
  have h : ((130823462494456373 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((829 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-57 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((829 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-57 / 16 : ℚ) : ℝ) ≤ ((16352932811807047 / 2305843009213693952 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_829 : ((119715353914795 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((829 / 8 : ℚ) : ℝ) ∧
    logKernel ((829 / 8 : ℚ) : ℝ) ≤ ((478861415659185 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_829
  constructor
  · exact (show ((119715353914795 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((130823462494456373 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((829 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((16352932811807047 / 2305843009213693952 : ℚ) : ℝ) ≤ ((478861415659185 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_830 : ((14431412554593717 / 2305843009213693952 : ℚ) : ℝ) ≤ heightZ ((415 / 4 : ℚ) : ℝ) ∧
    heightZ ((415 / 4 : ℚ) : ℝ) ≤ ((115451300436749739 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((14431412554593717 / 2305843009213693952 : ℚ) : ℝ) ≤ Real.exp (-((415 / 4 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-59 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((415 / 4 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-59 / 16 : ℚ) : ℝ) ≤ ((115451300436749739 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_830 : ((186468822749025 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((415 / 4 : ℚ) : ℝ) ∧
    logKernel ((415 / 4 : ℚ) : ℝ) ≤ ((372937645498055 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_830
  constructor
  · exact (show ((186468822749025 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((14431412554593717 / 2305843009213693952 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((415 / 4 : ℚ) : ℝ)) hh).trans
      (show zKernel ((115451300436749739 / 18446744073709551616 : ℚ) : ℝ) ≤ ((372937645498055 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_831 : ((25471353758698797 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((831 / 8 : ℚ) : ℝ) ∧
    heightZ ((831 / 8 : ℚ) : ℝ) ≤ ((101885415034795191 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((25471353758698797 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((831 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-61 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((831 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-61 / 16 : ℚ) : ℝ) ≤ ((101885415034795191 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_831 : ((290444130350687 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((831 / 8 : ℚ) : ℝ) ∧
    logKernel ((831 / 8 : ℚ) : ℝ) ≤ ((72611032587673 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_831
  constructor
  · exact (show ((290444130350687 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((25471353758698797 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((831 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((101885415034795191 / 18446744073709551616 : ℚ) : ℝ) ≤ ((72611032587673 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_832 : ((89913563186752721 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((104 / 1 : ℚ) : ℝ) ∧
    heightZ ((104 / 1 : ℚ) : ℝ) ≤ ((22478390796688181 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((89913563186752721 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((104 / 1 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-63 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((104 / 1 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-63 / 16 : ℚ) : ℝ) ≤ ((22478390796688181 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_832 : ((28274764519451 / 9007199254740992 : ℚ) : ℝ) ≤ logKernel ((104 / 1 : ℚ) : ℝ) ∧
    logKernel ((104 / 1 : ℚ) : ℝ) ≤ ((226198116155613 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_832
  constructor
  · exact (show ((28274764519451 / 9007199254740992 : ℚ) : ℝ) ≤ zKernel ((89913563186752721 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((104 / 1 : ℚ) : ℝ)) hh).trans
      (show zKernel ((22478390796688181 / 4611686018427387904 : ℚ) : ℝ) ≤ ((226198116155613 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_833 : ((79348441012653579 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((833 / 8 : ℚ) : ℝ) ∧
    heightZ ((833 / 8 : ℚ) : ℝ) ≤ ((39674220506326791 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((79348441012653579 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((833 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-65 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((833 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-65 / 16 : ℚ) : ℝ) ≤ ((39674220506326791 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_833 : ((176163269991263 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((833 / 8 : ℚ) : ℝ) ∧
    logKernel ((833 / 8 : ℚ) : ℝ) ≤ ((44040817497817 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_833
  constructor
  · exact (show ((176163269991263 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((79348441012653579 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((833 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((39674220506326791 / 9223372036854775808 : ℚ) : ℝ) ≤ ((44040817497817 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_834 : ((17506188354645815 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((417 / 4 : ℚ) : ℝ) ∧
    heightZ ((417 / 4 : ℚ) : ℝ) ≤ ((70024753418583263 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((17506188354645815 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((417 / 4 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-67 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((417 / 4 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-67 / 16 : ℚ) : ℝ) ≤ ((70024753418583263 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_834 : ((137196092617615 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((417 / 4 : ℚ) : ℝ) ∧
    logKernel ((417 / 4 : ℚ) : ℝ) ≤ ((34299023154405 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_834
  constructor
  · exact (show ((137196092617615 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((17506188354645815 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((417 / 4 : ℚ) : ℝ)) hh).trans
      (show zKernel ((70024753418583263 / 18446744073709551616 : ℚ) : ℝ) ≤ ((34299023154405 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_835 : ((61796627996149785 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((835 / 8 : ℚ) : ℝ) ∧
    heightZ ((835 / 8 : ℚ) : ℝ) ≤ ((15449156999037447 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((61796627996149785 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((835 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-69 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((835 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-69 / 16 : ℚ) : ℝ) ≤ ((15449156999037447 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_835 : ((106848424364935 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((835 / 8 : ℚ) : ℝ) ∧
    logKernel ((835 / 8 : ℚ) : ℝ) ≤ ((26712106091235 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_835
  constructor
  · exact (show ((106848424364935 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((61796627996149785 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((835 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((15449156999037447 / 4611686018427387904 : ℚ) : ℝ) ≤ ((26712106091235 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_836 : ((27267666398387339 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((209 / 2 : ℚ) : ℝ) ∧
    heightZ ((209 / 2 : ℚ) : ℝ) ≤ ((54535332796774681 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((27267666398387339 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((209 / 2 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-71 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((209 / 2 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-71 / 16 : ℚ) : ℝ) ≤ ((54535332796774681 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_836 : ((20803409141339 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((209 / 2 : ℚ) : ℝ) ∧
    logKernel ((209 / 2 : ℚ) : ℝ) ≤ ((83213636565361 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_836
  constructor
  · exact (show ((20803409141339 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((27267666398387339 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((209 / 2 : ℚ) : ℝ)) hh).trans
      (show zKernel ((54535332796774681 / 18446744073709551616 : ℚ) : ℝ) ≤ ((83213636565361 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_837 : ((48127262274573753 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((837 / 8 : ℚ) : ℝ) ∧
    heightZ ((837 / 8 : ℚ) : ℝ) ≤ ((12031815568643439 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((48127262274573753 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((837 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-73 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((837 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-73 / 16 : ℚ) : ℝ) ≤ ((12031815568643439 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_837 : ((32403422659659 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((837 / 8 : ℚ) : ℝ) ∧
    logKernel ((837 / 8 : ℚ) : ℝ) ≤ ((64806845319323 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_837
  constructor
  · exact (show ((32403422659659 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((48127262274573753 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((837 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((12031815568643439 / 4611686018427387904 : ℚ) : ℝ) ≤ ((64806845319323 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_838 : ((42472159887187787 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((419 / 4 : ℚ) : ℝ) ∧
    heightZ ((419 / 4 : ℚ) : ℝ) ≤ ((21236079943593895 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((42472159887187787 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((419 / 4 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-75 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((419 / 4 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-75 / 16 : ℚ) : ℝ) ≤ ((21236079943593895 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_838 : ((788619091923 / 1125899906842624 : ℚ) : ℝ) ≤ logKernel ((419 / 4 : ℚ) : ℝ) ∧
    logKernel ((419 / 4 : ℚ) : ℝ) ≤ ((50471621883077 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_838
  constructor
  · exact (show ((788619091923 / 1125899906842624 : ℚ) : ℝ) ≤ zKernel ((42472159887187787 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((419 / 4 : ℚ) : ℝ)) hh).trans
      (show zKernel ((21236079943593895 / 9223372036854775808 : ℚ) : ℝ) ≤ ((50471621883077 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_839 : ((37481549546520921 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((839 / 8 : ℚ) : ℝ) ∧
    heightZ ((839 / 8 : ℚ) : ℝ) ≤ ((9370387386630231 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((37481549546520921 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((839 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-77 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((839 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-77 / 16 : ℚ) : ℝ) ≤ ((9370387386630231 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_839 : ((9826834661355 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((839 / 8 : ℚ) : ℝ) ∧
    logKernel ((839 / 8 : ℚ) : ℝ) ≤ ((39307338645425 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_839
  constructor
  · exact (show ((9826834661355 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((37481549546520921 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((839 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((9370387386630231 / 4611686018427387904 : ℚ) : ℝ) ≤ ((39307338645425 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_840 : ((33077351378875759 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((105 / 1 : ℚ) : ℝ) ∧
    heightZ ((105 / 1 : ℚ) : ℝ) ≤ ((16538675689437881 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((33077351378875759 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((105 / 1 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-79 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((105 / 1 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-79 / 16 : ℚ) : ℝ) ≤ ((16538675689437881 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_840 : ((30612586117505 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((105 / 1 : ℚ) : ℝ) ∧
    logKernel ((105 / 1 : ℚ) : ℝ) ≤ ((15306293058755 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_840
  constructor
  · exact (show ((30612586117505 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((33077351378875759 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((105 / 1 : ℚ) : ℝ)) hh).trans
      (show zKernel ((16538675689437881 / 9223372036854775808 : ℚ) : ℝ) ≤ ((15306293058755 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_841 : ((29190660137560153 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((841 / 8 : ℚ) : ℝ) ∧
    heightZ ((841 / 8 : ℚ) : ℝ) ≤ ((7297665034390039 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((29190660137560153 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((841 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-81 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((841 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-81 / 16 : ℚ) : ℝ) ≤ ((7297665034390039 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_841 : ((23841106040153 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((841 / 8 : ℚ) : ℝ) ∧
    logKernel ((841 / 8 : ℚ) : ℝ) ≤ ((11920553020079 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_841
  constructor
  · exact (show ((23841106040153 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((29190660137560153 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((841 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((7297665034390039 / 4611686018427387904 : ℚ) : ℝ) ≤ ((11920553020079 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_842 : ((12880333577898227 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((421 / 4 : ℚ) : ℝ) ∧
    heightZ ((421 / 4 : ℚ) : ℝ) ≤ ((25760667155796457 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((12880333577898227 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((421 / 4 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-83 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((421 / 4 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-83 / 16 : ℚ) : ℝ) ≤ ((25760667155796457 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_842 : ((18567472053359 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((421 / 4 : ℚ) : ℝ) ∧
    logKernel ((421 / 4 : ℚ) : ℝ) ≤ ((4641868013341 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_842
  constructor
  · exact (show ((18567472053359 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((12880333577898227 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((421 / 4 : ℚ) : ℝ)) hh).trans
      (show zKernel ((25760667155796457 / 18446744073709551616 : ℚ) : ℝ) ≤ ((4641868013341 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_843 : ((11366854486751545 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((843 / 8 : ℚ) : ℝ) ∧
    heightZ ((843 / 8 : ℚ) : ℝ) ≤ ((22733708973503093 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((11366854486751545 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((843 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-85 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((843 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-85 / 16 : ℚ) : ℝ) ≤ ((22733708973503093 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_843 : ((3615090443703 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((843 / 8 : ℚ) : ℝ) ∧
    logKernel ((843 / 8 : ℚ) : ℝ) ≤ ((14460361774817 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_843
  constructor
  · exact (show ((3615090443703 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((11366854486751545 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((843 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((22733708973503093 / 18446744073709551616 : ℚ) : ℝ) ≤ ((14460361774817 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_844 : ((10031213876688049 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((211 / 2 : ℚ) : ℝ) ∧
    heightZ ((211 / 2 : ℚ) : ℝ) ≤ ((20062427753376101 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((10031213876688049 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((211 / 2 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-87 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((211 / 2 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-87 / 16 : ℚ) : ℝ) ≤ ((20062427753376101 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_844 : ((11261741073719 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((211 / 2 : ℚ) : ℝ) ∧
    logKernel ((211 / 2 : ℚ) : ℝ) ≤ ((2815435268431 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_844
  constructor
  · exact (show ((11261741073719 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((10031213876688049 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((211 / 2 : ℚ) : ℝ)) hh).trans
      (show zKernel ((20062427753376101 / 18446744073709551616 : ℚ) : ℝ) ≤ ((2815435268431 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_845 : ((8852515175340815 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((845 / 8 : ℚ) : ℝ) ∧
    heightZ ((845 / 8 : ℚ) : ℝ) ≤ ((17705030350681633 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((8852515175340815 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((845 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-89 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((845 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-89 / 16 : ℚ) : ℝ) ≤ ((17705030350681633 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_845 : ((8770652766959 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((845 / 8 : ℚ) : ℝ) ∧
    logKernel ((845 / 8 : ℚ) : ℝ) ≤ ((2192663191741 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_845
  constructor
  · exact (show ((8770652766959 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((8852515175340815 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((845 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((17705030350681633 / 18446744073709551616 : ℚ) : ℝ) ≤ ((2192663191741 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_846 : ((15624634444642791 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((423 / 4 : ℚ) : ℝ) ∧
    heightZ ((423 / 4 : ℚ) : ℝ) ≤ ((7812317222321397 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((15624634444642791 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((423 / 4 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-91 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((423 / 4 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-91 / 16 : ℚ) : ℝ) ≤ ((7812317222321397 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_846 : ((6830591242955 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((423 / 4 : ℚ) : ℝ) ∧
    logKernel ((423 / 4 : ℚ) : ℝ) ≤ ((426911952685 / 4503599627370496 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_846
  constructor
  · exact (show ((6830591242955 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((15624634444642791 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((423 / 4 : ℚ) : ℝ)) hh).trans
      (show zKernel ((7812317222321397 / 9223372036854775808 : ℚ) : ℝ) ≤ ((426911952685 / 4503599627370496 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_847 : ((13788691501413843 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((847 / 8 : ℚ) : ℝ) ∧
    heightZ ((847 / 8 : ℚ) : ℝ) ≤ ((6894345750706923 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((13788691501413843 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((847 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-93 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((847 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-93 / 16 : ℚ) : ℝ) ≤ ((6894345750706923 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_847 : ((5319669808853 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((847 / 8 : ℚ) : ℝ) ∧
    logKernel ((847 / 8 : ℚ) : ℝ) ≤ ((2659834904429 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_847
  constructor
  · exact (show ((5319669808853 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((13788691501413843 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((847 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((6894345750706923 / 9223372036854775808 : ℚ) : ℝ) ≤ ((2659834904429 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_848 : ((6084238770346125 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((106 / 1 : ℚ) : ℝ) ∧
    heightZ ((106 / 1 : ℚ) : ℝ) ≤ ((12168477540692253 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((6084238770346125 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((106 / 1 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-95 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((106 / 1 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-95 / 16 : ℚ) : ℝ) ≤ ((12168477540692253 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_848 : ((258935188301 / 4503599627370496 : ℚ) : ℝ) ≤ logKernel ((106 / 1 : ℚ) : ℝ) ∧
    logKernel ((106 / 1 : ℚ) : ℝ) ≤ ((4142963012821 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_848
  constructor
  · exact (show ((258935188301 / 4503599627370496 : ℚ) : ℝ) ≤ zKernel ((6084238770346125 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((106 / 1 : ℚ) : ℝ)) hh).trans
      (show zKernel ((12168477540692253 / 18446744073709551616 : ℚ) : ℝ) ≤ ((4142963012821 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_849 : ((5369321869415563 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((849 / 8 : ℚ) : ℝ) ∧
    heightZ ((849 / 8 : ℚ) : ℝ) ≤ ((10738643738831129 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((5369321869415563 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((849 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-97 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((849 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-97 / 16 : ℚ) : ℝ) ≤ ((10738643738831129 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_849 : ((403317854827 / 9007199254740992 : ℚ) : ℝ) ≤ logKernel ((849 / 8 : ℚ) : ℝ) ∧
    logKernel ((849 / 8 : ℚ) : ℝ) ≤ ((3226542838621 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_849
  constructor
  · exact (show ((403317854827 / 9007199254740992 : ℚ) : ℝ) ≤ zKernel ((5369321869415563 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((849 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((10738643738831129 / 18446744073709551616 : ℚ) : ℝ) ≤ ((3226542838621 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_850 : ((9476819837477927 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((425 / 4 : ℚ) : ℝ) ∧
    heightZ ((425 / 4 : ℚ) : ℝ) ≤ ((4738409918738965 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((9476819837477927 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((425 / 4 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-99 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((425 / 4 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-99 / 16 : ℚ) : ℝ) ≤ ((4738409918738965 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_850 : ((2512834089327 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((425 / 4 : ℚ) : ℝ) ∧
    logKernel ((425 / 4 : ℚ) : ℝ) ≤ ((628208522333 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_850
  constructor
  · exact (show ((2512834089327 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((9476819837477927 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((425 / 4 : ℚ) : ℝ)) hh).trans
      (show zKernel ((4738409918738965 / 9223372036854775808 : ℚ) : ℝ) ≤ ((628208522333 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_851 : ((8363264152926519 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((851 / 8 : ℚ) : ℝ) ∧
    heightZ ((851 / 8 : ℚ) : ℝ) ≤ ((4181632076463261 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((8363264152926519 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((851 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-101 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((851 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-101 / 16 : ℚ) : ℝ) ≤ ((4181632076463261 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_851 : ((122312322281 / 4503599627370496 : ℚ) : ℝ) ≤ logKernel ((851 / 8 : ℚ) : ℝ) ∧
    logKernel ((851 / 8 : ℚ) : ℝ) ≤ ((1956997156501 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_851
  constructor
  · exact (show ((122312322281 / 4503599627370496 : ℚ) : ℝ) ≤ zKernel ((8363264152926519 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((851 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((4181632076463261 / 9223372036854775808 : ℚ) : ℝ) ≤ ((1956997156501 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_852 : ((7380554710454433 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((213 / 2 : ℚ) : ℝ) ∧
    heightZ ((213 / 2 : ℚ) : ℝ) ≤ ((1845138677613609 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((7380554710454433 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((213 / 2 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-103 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((213 / 2 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-103 / 16 : ℚ) : ℝ) ≤ ((1845138677613609 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_852 : ((1524110917947 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((213 / 2 : ℚ) : ℝ) ∧
    logKernel ((213 / 2 : ℚ) : ℝ) ≤ ((23814233093 / 1125899906842624 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_852
  constructor
  · exact (show ((1524110917947 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((7380554710454433 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((213 / 2 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1845138677613609 / 4611686018427387904 : ℚ) : ℝ) ≤ ((23814233093 / 1125899906842624 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_853 : ((3256658335666091 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((853 / 8 : ℚ) : ℝ) ∧
    heightZ ((853 / 8 : ℚ) : ℝ) ≤ ((6513316671332185 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((3256658335666091 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((853 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-105 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((853 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-105 / 16 : ℚ) : ℝ) ≤ ((6513316671332185 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_853 : ((18546543381 / 1125899906842624 : ℚ) : ℝ) ≤ logKernel ((853 / 8 : ℚ) : ℝ) ∧
    logKernel ((853 / 8 : ℚ) : ℝ) ≤ ((1186978776389 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_853
  constructor
  · exact (show ((18546543381 / 1125899906842624 : ℚ) : ℝ) ≤ zKernel ((3256658335666091 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((853 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((6513316671332185 / 18446744073709551616 : ℚ) : ℝ) ≤ ((1186978776389 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_854 : ((2873990894001629 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((427 / 4 : ℚ) : ℝ) ∧
    heightZ ((427 / 4 : ℚ) : ℝ) ≤ ((5747981788003261 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((2873990894001629 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((427 / 4 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-107 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((427 / 4 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-107 / 16 : ℚ) : ℝ) ≤ ((5747981788003261 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_854 : ((924420000537 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((427 / 4 : ℚ) : ℝ) ∧
    logKernel ((427 / 4 : ℚ) : ℝ) ≤ ((462210000271 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_854
  constructor
  · exact (show ((924420000537 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((2873990894001629 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((427 / 4 : ℚ) : ℝ)) hh).trans
      (show zKernel ((5747981788003261 / 18446744073709551616 : ℚ) : ℝ) ≤ ((462210000271 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_855 : ((5072576124025539 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((855 / 8 : ℚ) : ℝ) ∧
    heightZ ((855 / 8 : ℚ) : ℝ) ≤ ((2536288062012771 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((5072576124025539 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((855 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-109 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((855 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-109 / 16 : ℚ) : ℝ) ≤ ((2536288062012771 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_855 : ((44996188769 / 4503599627370496 : ℚ) : ℝ) ≤ logKernel ((855 / 8 : ℚ) : ℝ) ∧
    logKernel ((855 / 8 : ℚ) : ℝ) ≤ ((719939020309 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_855
  constructor
  · exact (show ((44996188769 / 4503599627370496 : ℚ) : ℝ) ≤ zKernel ((5072576124025539 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((855 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((2536288062012771 / 9223372036854775808 : ℚ) : ℝ) ≤ ((719939020309 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_856 : ((4476532717577111 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((107 / 1 : ℚ) : ℝ) ∧
    heightZ ((107 / 1 : ℚ) : ℝ) ≤ ((2238266358788557 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((4476532717577111 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((107 / 1 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-111 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((107 / 1 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-111 / 16 : ℚ) : ℝ) ≤ ((2238266358788557 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_856 : ((70086134097 / 9007199254740992 : ℚ) : ℝ) ≤ logKernel ((107 / 1 : ℚ) : ℝ) ∧
    logKernel ((107 / 1 : ℚ) : ℝ) ≤ ((560689072781 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_856
  constructor
  · exact (show ((70086134097 / 9007199254740992 : ℚ) : ℝ) ≤ zKernel ((4476532717577111 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((107 / 1 : ℚ) : ℝ)) hh).trans
      (show zKernel ((2238266358788557 / 9223372036854775808 : ℚ) : ℝ) ≤ ((560689072781 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_857 : ((1975263128790201 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((857 / 8 : ℚ) : ℝ) ∧
    heightZ ((857 / 8 : ℚ) : ℝ) ≤ ((3950526257580405 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((1975263128790201 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((857 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-113 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((857 / 8 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-113 / 16 : ℚ) : ℝ) ≤ ((3950526257580405 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_857 : ((436665088937 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((857 / 8 : ℚ) : ℝ) ∧
    logKernel ((857 / 8 : ℚ) : ℝ) ≤ ((218332544471 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_857
  constructor
  · exact (show ((436665088937 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((1975263128790201 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((857 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((3950526257580405 / 18446744073709551616 : ℚ) : ℝ) ≤ ((218332544471 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_858 : ((1743163592946909 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((429 / 4 : ℚ) : ℝ) ∧
    heightZ ((429 / 4 : ℚ) : ℝ) ≤ ((3486327185893821 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((1743163592946909 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((429 / 4 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-115 / 16 : ℚ) : ℝ) ∧
      Real.exp (-((429 / 4 : ℚ) : ℝ)) + ((1 / 4 : ℚ) : ℝ) * Real.exp ((-115 / 16 : ℚ) : ℝ) ≤ ((3486327185893821 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_858 : ((85018778301 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((429 / 4 : ℚ) : ℝ) ∧
    logKernel ((429 / 4 : ℚ) : ℝ) ≤ ((340075113209 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_858
  constructor
  · exact (show ((85018778301 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((1743163592946909 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((429 / 4 : ℚ) : ℝ)) hh).trans
      (show zKernel ((3486327185893821 / 18446744073709551616 : ℚ) : ℝ) ≤ ((340075113209 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

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

theorem log_height_bounds_32 : ((334316367778222041 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((207 / 2 : ℚ) : ℝ) ∧
    Real.log ((207 / 2 : ℚ) : ℝ) ≤ ((83579091944555511 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((334316367778222041 / 72057594037927936 : ℚ) : ℝ) ≤ ((207 / 2 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((207 / 2 : ℚ) : ℝ) ≤ Real.exp ((83579091944555511 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_32 : heightPower (32 : Fin 125) ≤ ((1165185823278353 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_32
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_32 : heightFactor (32 : Fin 125) ≤ ((29043287578619047 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_32
  obtain ⟨hpl, hph⟩ := kernel_bounds_827
  obtain ⟨hcl, hch⟩ := kernel_bounds_828
  obtain ⟨hzl, hzh⟩ := height_z_bounds_828
  have h : (((42849 / 2 : ℚ) : ℝ) * (logKernel ((827 / 8 : ℚ) : ℝ) - logKernel ((207 / 2 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((207 / 2 : ℚ) : ℝ) + Real.log ((207 / 2 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((29043287578619047 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_33 : ((167201670674135779 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((829 / 8 : ℚ) : ℝ) ∧
    Real.log ((829 / 8 : ℚ) : ℝ) ≤ ((334403341348271561 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((167201670674135779 / 36028797018963968 : ℚ) : ℝ) ≤ ((829 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((829 / 8 : ℚ) : ℝ) ≤ Real.exp ((334403341348271561 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_33 : heightPower (33 : Fin 125) ≤ ((1200709935875191 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_33
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_33 : heightFactor (33 : Fin 125) ≤ ((47295614499798301 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_33
  obtain ⟨hpl, hph⟩ := kernel_bounds_828
  obtain ⟨hcl, hch⟩ := kernel_bounds_829
  obtain ⟨hzl, hzh⟩ := height_z_bounds_829
  have h : (((687241 / 32 : ℚ) : ℝ) * (logKernel ((207 / 2 : ℚ) : ℝ) - logKernel ((829 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((829 / 8 : ℚ) : ℝ) + Real.log ((829 / 8 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((47295614499798301 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_34 : ((334490210067698857 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((415 / 4 : ℚ) : ℝ) ∧
    Real.log ((415 / 4 : ℚ) : ℝ) ≤ ((83622552516924715 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((334490210067698857 / 72057594037927936 : ℚ) : ℝ) ≤ ((415 / 4 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((415 / 4 : ℚ) : ℝ) ≤ Real.exp ((83622552516924715 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_34 : heightPower (34 : Fin 125) ≤ ((618116819449643 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_34
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_34 : heightFactor (34 : Fin 125) ≤ ((1203412508714401 / 8796093022208 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_34
  obtain ⟨hpl, hph⟩ := kernel_bounds_829
  obtain ⟨hcl, hch⟩ := kernel_bounds_830
  obtain ⟨hzl, hzh⟩ := height_z_bounds_830
  have h : (((172225 / 8 : ℚ) : ℝ) * (logKernel ((829 / 8 : ℚ) : ℝ) - logKernel ((415 / 4 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((415 / 4 : ℚ) : ℝ) + Real.log ((415 / 4 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((1203412508714401 / 8796093022208 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_35 : ((334576974189004025 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((831 / 8 : ℚ) : ℝ) ∧
    Real.log ((831 / 8 : ℚ) : ℝ) ≤ ((83644243547251007 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((334576974189004025 / 72057594037927936 : ℚ) : ℝ) ≤ ((831 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((831 / 8 : ℚ) : ℝ) ≤ Real.exp ((83644243547251007 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_35 : heightPower (35 : Fin 125) ≤ ((635878466668483 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_35
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_35 : heightFactor (35 : Fin 125) ≤ ((31354989230288005 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_35
  obtain ⟨hpl, hph⟩ := kernel_bounds_830
  obtain ⟨hcl, hch⟩ := kernel_bounds_831
  obtain ⟨hzl, hzh⟩ := height_z_bounds_831
  have h : (((690561 / 32 : ℚ) : ℝ) * (logKernel ((415 / 4 : ℚ) : ℝ) - logKernel ((831 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((831 / 8 : ℚ) : ℝ) + Real.log ((831 / 8 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((31354989230288005 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_36 : ((334663633963776139 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((104 / 1 : ℚ) : ℝ) ∧
    Real.log ((104 / 1 : ℚ) : ℝ) ≤ ((167331816981888071 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((334663633963776139 / 72057594037927936 : ℚ) : ℝ) ≤ ((104 / 1 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((104 / 1 : ℚ) : ℝ) ≤ Real.exp ((167331816981888071 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_36 : heightPower (36 : Fin 125) ≤ ((653639910085501 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_36
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_36 : heightFactor (36 : Fin 125) ≤ ((25529796012521225 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_36
  obtain ⟨hpl, hph⟩ := kernel_bounds_831
  obtain ⟨hcl, hch⟩ := kernel_bounds_832
  obtain ⟨hzl, hzh⟩ := height_z_bounds_832
  have h : (((21632 / 1 : ℚ) : ℝ) * (logKernel ((831 / 8 : ℚ) : ℝ) - logKernel ((104 / 1 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((104 / 1 : ℚ) : ℝ) + Real.log ((104 / 1 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((25529796012521225 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_37 : ((167375094821348827 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((833 / 8 : ℚ) : ℝ) ∧
    Real.log ((833 / 8 : ℚ) : ℝ) ≤ ((334750189642697657 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((167375094821348827 / 36028797018963968 : ℚ) : ℝ) ≤ ((833 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((833 / 8 : ℚ) : ℝ) ≤ Real.exp ((334750189642697657 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_37 : heightPower (37 : Fin 125) ≤ ((1342802300380621 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_37
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_37 : heightFactor (37 : Fin 125) ≤ ((20786748886556387 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_37
  obtain ⟨hpl, hph⟩ := kernel_bounds_832
  obtain ⟨hcl, hch⟩ := kernel_bounds_833
  obtain ⟨hzl, hzh⟩ := height_z_bounds_833
  have h : (((693889 / 32 : ℚ) : ℝ) * (logKernel ((104 / 1 : ℚ) : ℝ) - logKernel ((833 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((833 / 8 : ℚ) : ℝ) + Real.log ((833 / 8 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((20786748886556387 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_38 : ((41854580184443593 / 9007199254740992 : ℚ) : ℝ) ≤ Real.log ((417 / 4 : ℚ) : ℝ) ∧
    Real.log ((417 / 4 : ℚ) : ℝ) ≤ ((334836641475548747 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((41854580184443593 / 9007199254740992 : ℚ) : ℝ) ≤ ((417 / 4 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((417 / 4 : ℚ) : ℝ) ≤ Real.exp ((334836641475548747 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_38 : heightPower (38 : Fin 125) ≤ ((172290546867691 / 35184372088832 : ℚ) : ℝ) := by
  have hh := log_height_bounds_38
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_38 : heightFactor (38 : Fin 125) ≤ ((16924830738255761 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_38
  obtain ⟨hpl, hph⟩ := kernel_bounds_833
  obtain ⟨hcl, hch⟩ := kernel_bounds_834
  obtain ⟨hzl, hzh⟩ := height_z_bounds_834
  have h : (((173889 / 8 : ℚ) : ℝ) * (logKernel ((833 / 8 : ℚ) : ℝ) - logKernel ((417 / 4 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((417 / 4 : ℚ) : ℝ) + Real.log ((417 / 4 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((16924830738255761 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_39 : ((20932686856950727 / 4503599627370496 : ℚ) : ℝ) ≤ Real.log ((835 / 8 : ℚ) : ℝ) ∧
    Real.log ((835 / 8 : ℚ) : ℝ) ≤ ((334922989711211635 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((20932686856950727 / 4503599627370496 : ℚ) : ℝ) ≤ ((835 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((835 / 8 : ℚ) : ℝ) ≤ Real.exp ((334922989711211635 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_39 : heightPower (39 : Fin 125) ≤ ((706923022412959 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_39
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_39 : heightFactor (39 : Fin 125) ≤ ((6890181243590191 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_39
  obtain ⟨hpl, hph⟩ := kernel_bounds_834
  obtain ⟨hcl, hch⟩ := kernel_bounds_835
  obtain ⟨hzl, hzh⟩ := height_z_bounds_835
  have h : (((697225 / 32 : ℚ) : ℝ) * (logKernel ((417 / 4 : ℚ) : ℝ) - logKernel ((835 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((835 / 8 : ℚ) : ℝ) + Real.log ((835 / 8 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((6890181243590191 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_40 : ((167504617298837445 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((209 / 2 : ℚ) : ℝ) ∧
    Real.log ((209 / 2 : ℚ) : ℝ) ≤ ((335009234597674893 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((167504617298837445 / 36028797018963968 : ℚ) : ℝ) ≤ ((209 / 2 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((209 / 2 : ℚ) : ℝ) ≤ Real.exp ((335009234597674893 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_40 : heightPower (40 : Fin 125) ≤ ((1449367311002497 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_40
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_40 : heightFactor (40 : Fin 125) ≤ ((5610034088437973 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_40
  obtain ⟨hpl, hph⟩ := kernel_bounds_835
  obtain ⟨hcl, hch⟩ := kernel_bounds_836
  obtain ⟨hzl, hzh⟩ := height_z_bounds_836
  have h : (((43681 / 2 : ℚ) : ℝ) * (logKernel ((835 / 8 : ℚ) : ℝ) - logKernel ((209 / 2 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((209 / 2 : ℚ) : ℝ) + Real.log ((209 / 2 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((5610034088437973 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_41 : ((83773844095509427 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((837 / 8 : ℚ) : ℝ) ∧
    Real.log ((837 / 8 : ℚ) : ℝ) ≤ ((335095376382037711 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((83773844095509427 / 18014398509481984 : ℚ) : ℝ) ≤ ((837 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((837 / 8 : ℚ) : ℝ) ≤ Real.exp ((335095376382037711 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_41 : heightPower (41 : Fin 125) ≤ ((92805510902281 / 17592186044416 : ℚ) : ℝ) := by
  have hh := log_height_bounds_41
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_41 : heightFactor (41 : Fin 125) ≤ ((4567714010273327 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_41
  obtain ⟨hpl, hph⟩ := kernel_bounds_836
  obtain ⟨hcl, hch⟩ := kernel_bounds_837
  obtain ⟨hzl, hzh⟩ := height_z_bounds_837
  have h : (((700569 / 32 : ℚ) : ℝ) * (logKernel ((209 / 2 : ℚ) : ℝ) - logKernel ((837 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((837 / 8 : ℚ) : ℝ) + Real.log ((837 / 8 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((4567714010273327 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_42 : ((335181415310514145 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((419 / 4 : ℚ) : ℝ) ∧
    Real.log ((419 / 4 : ℚ) : ℝ) ≤ ((83795353827628537 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((335181415310514145 / 72057594037927936 : ℚ) : ℝ) ≤ ((419 / 4 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((419 / 4 : ℚ) : ℝ) ≤ Real.exp ((83795353827628537 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_42 : heightPower (42 : Fin 125) ≤ ((1520408636089689 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_42
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_42 : heightFactor (42 : Fin 125) ≤ ((3719040109327661 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_42
  obtain ⟨hpl, hph⟩ := kernel_bounds_837
  obtain ⟨hcl, hch⟩ := kernel_bounds_838
  obtain ⟨hzl, hzh⟩ := height_z_bounds_838
  have h : (((175561 / 8 : ℚ) : ℝ) * (logKernel ((837 / 8 : ℚ) : ℝ) - logKernel ((419 / 4 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((419 / 4 : ℚ) : ℝ) + Real.log ((419 / 4 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((3719040109327661 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_43 : ((335267351628437351 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((839 / 8 : ℚ) : ℝ) ∧
    Real.log ((839 / 8 : ℚ) : ℝ) ≤ ((167633675814218677 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((335267351628437351 / 72057594037927936 : ℚ) : ℝ) ≤ ((839 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((839 / 8 : ℚ) : ℝ) ≤ Real.exp ((167633675814218677 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_43 : heightPower (43 : Fin 125) ≤ ((1555928696920409 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_43
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_43 : heightFactor (43 : Fin 125) ≤ ((6056076780171877 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_43
  obtain ⟨hpl, hph⟩ := kernel_bounds_838
  obtain ⟨hcl, hch⟩ := kernel_bounds_839
  obtain ⟨hzl, hzh⟩ := height_z_bounds_839
  have h : (((703921 / 32 : ℚ) : ℝ) * (logKernel ((419 / 4 : ℚ) : ℝ) - logKernel ((839 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((839 / 8 : ℚ) : ℝ) + Real.log ((839 / 8 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((6056076780171877 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_44 : ((83838296395065941 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((105 / 1 : ℚ) : ℝ) ∧
    Real.log ((105 / 1 : ℚ) : ℝ) ≤ ((335353185580263767 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((83838296395065941 / 18014398509481984 : ℚ) : ℝ) ≤ ((105 / 1 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((105 / 1 : ℚ) : ℝ) ≤ Real.exp ((335353185580263767 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_44 : heightPower (44 : Fin 125) ≤ ((1591448357883563 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_44
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_44 : heightFactor (44 : Fin 125) ≤ ((4930834747272815 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_44
  obtain ⟨hpl, hph⟩ := kernel_bounds_839
  obtain ⟨hcl, hch⟩ := kernel_bounds_840
  obtain ⟨hzl, hzh⟩ := height_z_bounds_840
  have h : (((22050 / 1 : ℚ) : ℝ) * (logKernel ((839 / 8 : ℚ) : ℝ) - logKernel ((105 / 1 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((105 / 1 : ℚ) : ℝ) + Real.log ((105 / 1 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((4930834747272815 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_45 : ((335438917409577281 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((841 / 8 : ℚ) : ℝ) ∧
    Real.log ((841 / 8 : ℚ) : ℝ) ≤ ((83859729352394321 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((335438917409577281 / 72057594037927936 : ℚ) : ℝ) ≤ ((841 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((841 / 8 : ℚ) : ℝ) ≤ Real.exp ((83859729352394321 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_45 : heightPower (45 : Fin 125) ≤ ((1626967619930651 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_45
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_45 : heightFactor (45 : Fin 125) ≤ ((4014653675502389 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_45
  obtain ⟨hpl, hph⟩ := kernel_bounds_840
  obtain ⟨hcl, hch⟩ := kernel_bounds_841
  obtain ⟨hzl, hzh⟩ := height_z_bounds_841
  have h : (((707281 / 32 : ℚ) : ℝ) * (logKernel ((105 / 1 : ℚ) : ℝ) - logKernel ((841 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((841 / 8 : ℚ) : ℝ) + Real.log ((841 / 8 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((4014653675502389 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_46 : ((10485142104971669 / 2251799813685248 : ℚ) : ℝ) ≤ Real.log ((421 / 4 : ℚ) : ℝ) ∧
    Real.log ((421 / 4 : ℚ) : ℝ) ≤ ((335524547359093411 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((10485142104971669 / 2251799813685248 : ℚ) : ℝ) ≤ ((421 / 4 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((421 / 4 : ℚ) : ℝ) ≤ Real.exp ((335524547359093411 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_46 : heightPower (46 : Fin 125) ≤ ((415621621002445 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_46
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_46 : heightFactor (46 : Fin 125) ≤ ((408586775586431 / 35184372088832 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_46
  obtain ⟨hpl, hph⟩ := kernel_bounds_841
  obtain ⟨hcl, hch⟩ := kernel_bounds_842
  obtain ⟨hzl, hzh⟩ := height_z_bounds_842
  have h : (((177241 / 8 : ℚ) : ℝ) * (logKernel ((841 / 8 : ℚ) : ℝ) - logKernel ((421 / 4 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((421 / 4 : ℚ) : ℝ) + Real.log ((421 / 4 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((408586775586431 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_47 : ((335610075670663381 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((843 / 8 : ℚ) : ℝ) ∧
    Real.log ((843 / 8 : ℚ) : ℝ) ≤ ((41951259458832923 / 9007199254740992 : ℚ) : ℝ) := by
  have hl : Real.exp ((335610075670663381 / 72057594037927936 : ℚ) : ℝ) ≤ ((843 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((843 / 8 : ℚ) : ℝ) ≤ Real.exp ((41951259458832923 / 9007199254740992 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_47 : heightPower (47 : Fin 125) ≤ ((849002475532841 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_47
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_47 : heightFactor (47 : Fin 125) ≤ ((2661332085734311 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_47
  obtain ⟨hpl, hph⟩ := kernel_bounds_842
  obtain ⟨hcl, hch⟩ := kernel_bounds_843
  obtain ⟨hzl, hzh⟩ := height_z_bounds_843
  have h : (((710649 / 32 : ℚ) : ℝ) * (logKernel ((421 / 4 : ℚ) : ℝ) - logKernel ((843 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((843 / 8 : ℚ) : ℝ) + Real.log ((843 / 8 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((2661332085734311 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_48 : ((167847751292639133 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((211 / 2 : ℚ) : ℝ) ∧
    Real.log ((211 / 2 : ℚ) : ℝ) ≤ ((335695502585278269 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((167847751292639133 / 36028797018963968 : ℚ) : ℝ) ≤ ((211 / 2 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((211 / 2 : ℚ) : ℝ) ≤ Real.exp ((335695502585278269 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_48 : heightPower (48 : Fin 125) ≤ ((1733523022039729 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_48
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_48 : heightFactor (48 : Fin 125) ≤ ((1083408965780557 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_48
  obtain ⟨hpl, hph⟩ := kernel_bounds_843
  obtain ⟨hcl, hch⟩ := kernel_bounds_844
  obtain ⟨hzl, hzh⟩ := height_z_bounds_844
  have h : (((44521 / 2 : ℚ) : ℝ) * (logKernel ((843 / 8 : ℚ) : ℝ) - logKernel ((211 / 2 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((211 / 2 : ℚ) : ℝ) + Real.log ((211 / 2 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((1083408965780557 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_49 : ((41972603542884129 / 9007199254740992 : ℚ) : ℝ) ≤ Real.log ((845 / 8 : ℚ) : ℝ) ∧
    Real.log ((845 / 8 : ℚ) : ℝ) ≤ ((335780828343073035 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((41972603542884129 / 9007199254740992 : ℚ) : ℝ) ≤ ((845 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((845 / 8 : ℚ) : ℝ) ≤ Real.exp ((335780828343073035 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_49 : heightPower (49 : Fin 125) ≤ ((1769040697869947 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_49
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_49 : heightFactor (49 : Fin 125) ≤ ((1764185910697509 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_49
  obtain ⟨hpl, hph⟩ := kernel_bounds_844
  obtain ⟨hcl, hch⟩ := kernel_bounds_845
  obtain ⟨hzl, hzh⟩ := height_z_bounds_845
  have h : (((714025 / 32 : ℚ) : ℝ) * (logKernel ((211 / 2 : ℚ) : ℝ) - logKernel ((845 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((845 / 8 : ℚ) : ℝ) + Real.log ((845 / 8 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((1764185910697509 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_50 : ((335866053183330601 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((423 / 4 : ℚ) : ℝ) ∧
    Real.log ((423 / 4 : ℚ) : ℝ) ≤ ((83966513295832651 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((335866053183330601 / 72057594037927936 : ℚ) : ℝ) ≤ ((423 / 4 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((423 / 4 : ℚ) : ℝ) ≤ Real.exp ((83966513295832651 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_50 : heightPower (50 : Fin 125) ≤ ((1804557979491035 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_50
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_50 : heightFactor (50 : Fin 125) ≤ ((1436365147034117 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_50
  obtain ⟨hpl, hph⟩ := kernel_bounds_845
  obtain ⟨hcl, hch⟩ := kernel_bounds_846
  obtain ⟨hzl, hzh⟩ := height_z_bounds_846
  have h : (((178929 / 8 : ℚ) : ℝ) * (logKernel ((845 / 8 : ℚ) : ℝ) - logKernel ((423 / 4 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((423 / 4 : ℚ) : ℝ) + Real.log ((423 / 4 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((1436365147034117 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_51 : ((335951177344485877 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((847 / 8 : ℚ) : ℝ) ∧
    Real.log ((847 / 8 : ℚ) : ℝ) ≤ ((41993897168060735 / 9007199254740992 : ℚ) : ℝ) := by
  have hl : Real.exp ((335951177344485877 / 72057594037927936 : ℚ) : ℝ) ≤ ((847 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((847 / 8 : ℚ) : ℝ) ≤ Real.exp ((41993897168060735 / 9007199254740992 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_51 : heightPower (51 : Fin 125) ≤ ((1840074867834379 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_51
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_51 : heightFactor (51 : Fin 125) ≤ ((1169456176379243 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_51
  obtain ⟨hpl, hph⟩ := kernel_bounds_846
  obtain ⟨hcl, hch⟩ := kernel_bounds_847
  obtain ⟨hzl, hzh⟩ := height_z_bounds_847
  have h : (((717409 / 32 : ℚ) : ℝ) * (logKernel ((423 / 4 : ℚ) : ℝ) - logKernel ((847 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((847 / 8 : ℚ) : ℝ) + Real.log ((847 / 8 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((1169456176379243 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_52 : ((336036201064129743 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((106 / 1 : ℚ) : ℝ) ∧
    Real.log ((106 / 1 : ℚ) : ℝ) ≤ ((168018100532064873 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((336036201064129743 / 72057594037927936 : ℚ) : ℝ) ≤ ((106 / 1 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((106 / 1 : ℚ) : ℝ) ≤ Real.exp ((168018100532064873 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_52 : heightPower (52 : Fin 125) ≤ ((937795681914035 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_52
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_52 : heightFactor (52 : Fin 125) ≤ ((952141802672933 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_52
  obtain ⟨hpl, hph⟩ := kernel_bounds_847
  obtain ⟨hcl, hch⟩ := kernel_bounds_848
  obtain ⟨hzl, hzh⟩ := height_z_bounds_848
  have h : (((22472 / 1 : ℚ) : ℝ) * (logKernel ((847 / 8 : ℚ) : ℝ) - logKernel ((106 / 1 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((106 / 1 : ℚ) : ℝ) + Real.log ((106 / 1 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((952141802672933 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_53 : ((336121124579013045 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((849 / 8 : ℚ) : ℝ) ∧
    Real.log ((849 / 8 : ℚ) : ℝ) ≤ ((42015140572376631 / 9007199254740992 : ℚ) : ℝ) := by
  have hl : Real.exp ((336121124579013045 / 72057594037927936 : ℚ) : ℝ) ≤ ((849 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((849 / 8 : ℚ) : ℝ) ≤ Real.exp ((42015140572376631 / 9007199254740992 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_53 : heightPower (53 : Fin 125) ≤ ((1911107468396915 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_53
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_53 : heightFactor (53 : Fin 125) ≤ ((387603695256517 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_53
  obtain ⟨hpl, hph⟩ := kernel_bounds_848
  obtain ⟨hcl, hch⟩ := kernel_bounds_849
  obtain ⟨hzl, hzh⟩ := height_z_bounds_849
  have h : (((720801 / 32 : ℚ) : ℝ) * (logKernel ((106 / 1 : ℚ) : ℝ) - logKernel ((849 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((849 / 8 : ℚ) : ℝ) + Real.log ((849 / 8 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((387603695256517 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_54 : ((168102974062525273 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((425 / 4 : ℚ) : ℝ) ∧
    Real.log ((425 / 4 : ℚ) : ℝ) ≤ ((336205948125050549 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((168102974062525273 / 36028797018963968 : ℚ) : ℝ) ≤ ((425 / 4 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((425 / 4 : ℚ) : ℝ) ≤ Real.exp ((336205948125050549 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_54 : heightPower (54 : Fin 125) ≤ ((243327897807807 / 35184372088832 : ℚ) : ℝ) := by
  have hh := log_height_bounds_54
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_54 : heightFactor (54 : Fin 125) ≤ ((315575133508309 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_54
  obtain ⟨hpl, hph⟩ := kernel_bounds_849
  obtain ⟨hcl, hch⟩ := kernel_bounds_850
  obtain ⟨hzl, hzh⟩ := height_z_bounds_850
  have h : (((180625 / 8 : ℚ) : ℝ) * (logKernel ((849 / 8 : ℚ) : ℝ) - logKernel ((425 / 4 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((425 / 4 : ℚ) : ℝ) + Real.log ((425 / 4 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((315575133508309 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_55 : ((168145335968662429 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((851 / 8 : ℚ) : ℝ) ∧
    Real.log ((851 / 8 : ℚ) : ℝ) ≤ ((336290671937324861 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((168145335968662429 / 36028797018963968 : ℚ) : ℝ) ≤ ((851 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((851 / 8 : ℚ) : ℝ) ≤ Real.exp ((336290671937324861 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_55 : heightPower (55 : Fin 125) ≤ ((1982138506942985 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_55
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_55 : heightFactor (55 : Fin 125) ≤ ((513861681370875 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_55
  obtain ⟨hpl, hph⟩ := kernel_bounds_850
  obtain ⟨hcl, hch⟩ := kernel_bounds_851
  obtain ⟨hzl, hzh⟩ := height_z_bounds_851
  have h : (((724201 / 32 : ℚ) : ℝ) * (logKernel ((425 / 4 : ℚ) : ℝ) - logKernel ((851 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((851 / 8 : ℚ) : ℝ) + Real.log ((851 / 8 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((513861681370875 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_56 : ((84093824062522587 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((213 / 2 : ℚ) : ℝ) ∧
    Real.log ((213 / 2 : ℚ) : ℝ) ≤ ((336375296250090351 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((84093824062522587 / 18014398509481984 : ℚ) : ℝ) ≤ ((213 / 2 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((213 / 2 : ℚ) : ℝ) ≤ Real.exp ((336375296250090351 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_56 : heightPower (56 : Fin 125) ≤ ((2017653442753557 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_56
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_56 : heightFactor (56 : Fin 125) ≤ ((26147990288339 / 17592186044416 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_56
  obtain ⟨hpl, hph⟩ := kernel_bounds_851
  obtain ⟨hcl, hch⟩ := kernel_bounds_852
  obtain ⟨hzl, hzh⟩ := height_z_bounds_852
  have h : (((45369 / 2 : ℚ) : ℝ) * (logKernel ((851 / 8 : ℚ) : ℝ) - logKernel ((213 / 2 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((213 / 2 : ℚ) : ℝ) + Real.log ((213 / 2 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((26147990288339 / 17592186044416 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_57 : ((168229910648388515 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((853 / 8 : ℚ) : ℝ) ∧
    Real.log ((853 / 8 : ℚ) : ℝ) ≤ ((336459821296777033 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((168229910648388515 / 36028797018963968 : ℚ) : ℝ) ≤ ((853 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((853 / 8 : ℚ) : ℝ) ≤ Real.exp ((336459821296777033 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_57 : heightPower (57 : Fin 125) ≤ ((2053167990806009 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_57
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_57 : heightFactor (57 : Fin 125) ≤ ((170309537714435 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_57
  obtain ⟨hpl, hph⟩ := kernel_bounds_852
  obtain ⟨hcl, hch⟩ := kernel_bounds_853
  obtain ⟨hzl, hzh⟩ := height_z_bounds_853
  have h : (((727609 / 32 : ℚ) : ℝ) * (logKernel ((213 / 2 : ℚ) : ℝ) - logKernel ((853 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((853 / 8 : ℚ) : ℝ) + Real.log ((853 / 8 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((170309537714435 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_58 : ((336544247309994425 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((427 / 4 : ℚ) : ℝ) ∧
    Real.log ((427 / 4 : ℚ) : ℝ) ≤ ((84136061827498607 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((336544247309994425 / 72057594037927936 : ℚ) : ℝ) ≤ ((427 / 4 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((427 / 4 : ℚ) : ℝ) ≤ Real.exp ((84136061827498607 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_58 : heightPower (58 : Fin 125) ≤ ((2088682152008971 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_58
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_58 : heightFactor (58 : Fin 125) ≤ ((277318116084111 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_58
  obtain ⟨hpl, hph⟩ := kernel_bounds_853
  obtain ⟨hcl, hch⟩ := kernel_bounds_854
  obtain ⟨hzl, hzh⟩ := height_z_bounds_854
  have h : (((182329 / 8 : ℚ) : ℝ) * (logKernel ((853 / 8 : ℚ) : ℝ) - logKernel ((427 / 4 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((427 / 4 : ℚ) : ℝ) + Real.log ((427 / 4 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((277318116084111 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_59 : ((336628574521535401 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((855 / 8 : ℚ) : ℝ) ∧
    Real.log ((855 / 8 : ℚ) : ℝ) ≤ ((84157143630383851 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((336628574521535401 / 72057594037927936 : ℚ) : ℝ) ≤ ((855 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((855 / 8 : ℚ) : ℝ) ≤ Real.exp ((84157143630383851 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_59 : heightPower (59 : Fin 125) ≤ ((2124195927267885 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_59
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_59 : heightFactor (59 : Fin 125) ≤ ((225780342388287 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_59
  obtain ⟨hpl, hph⟩ := kernel_bounds_854
  obtain ⟨hcl, hch⟩ := kernel_bounds_855
  obtain ⟨hzl, hzh⟩ := height_z_bounds_855
  have h : (((731025 / 32 : ℚ) : ℝ) * (logKernel ((427 / 4 : ℚ) : ℝ) - logKernel ((855 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((855 / 8 : ℚ) : ℝ) + Real.log ((855 / 8 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((225780342388287 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_60 : ((336712803162379995 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((107 / 1 : ℚ) : ℝ) ∧
    Real.log ((107 / 1 : ℚ) : ℝ) ≤ ((168356401581189999 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((336712803162379995 / 72057594037927936 : ℚ) : ℝ) ≤ ((107 / 1 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((107 / 1 : ℚ) : ℝ) ≤ Real.exp ((168356401581189999 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_60 : heightPower (60 : Fin 125) ≤ ((269963664685627 / 35184372088832 : ℚ) : ℝ) := by
  have hh := log_height_bounds_60
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_60 : heightFactor (60 : Fin 125) ≤ ((183819943060417 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_60
  obtain ⟨hpl, hph⟩ := kernel_bounds_855
  obtain ⟨hcl, hch⟩ := kernel_bounds_856
  obtain ⟨hzl, hzh⟩ := height_z_bounds_856
  have h : (((22898 / 1 : ℚ) : ℝ) * (logKernel ((855 / 8 : ℚ) : ℝ) - logKernel ((107 / 1 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((107 / 1 : ℚ) : ℝ) + Real.log ((107 / 1 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((183819943060417 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_61 : ((84199233365674801 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((857 / 8 : ℚ) : ℝ) ∧
    Real.log ((857 / 8 : ℚ) : ℝ) ≤ ((336796933462699207 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((84199233365674801 / 18014398509481984 : ℚ) : ℝ) ≤ ((857 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((857 / 8 : ℚ) : ℝ) ≤ Real.exp ((336796933462699207 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_61 : heightPower (61 : Fin 125) ≤ ((1097611161779735 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_61
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_61 : heightFactor (61 : Fin 125) ≤ ((149657244368715 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_61
  obtain ⟨hpl, hph⟩ := kernel_bounds_856
  obtain ⟨hcl, hch⟩ := kernel_bounds_857
  obtain ⟨hzl, hzh⟩ := height_z_bounds_857
  have h : (((734449 / 32 : ℚ) : ℝ) * (logKernel ((107 / 1 : ℚ) : ℝ) - logKernel ((857 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((857 / 8 : ℚ) : ℝ) + Real.log ((857 / 8 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((149657244368715 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_62 : ((336880965651858763 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((429 / 4 : ℚ) : ℝ) ∧
    Real.log ((429 / 4 : ℚ) : ℝ) ≤ ((168440482825929383 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((336880965651858763 / 72057594037927936 : ℚ) : ℝ) ≤ ((429 / 4 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((429 / 4 : ℚ) : ℝ) ≤ Real.exp ((168440482825929383 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_62 : heightPower (62 : Fin 125) ≤ ((2230734946387207 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_62
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_62 : heightFactor (62 : Fin 125) ≤ ((3807601624655 / 8796093022208 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_62
  obtain ⟨hpl, hph⟩ := kernel_bounds_857
  obtain ⟨hcl, hch⟩ := kernel_bounds_858
  obtain ⟨hzl, hzh⟩ := height_z_bounds_858
  have h : (((184041 / 8 : ℚ) : ℝ) * (logKernel ((857 / 8 : ℚ) : ℝ) - logKernel ((429 / 4 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((429 / 4 : ℚ) : ℝ) + Real.log ((429 / 4 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((3807601624655 / 8796093022208 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_63 : ((336964899958422897 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((859 / 8 : ℚ) : ℝ) ∧
    Real.log ((859 / 8 : ℚ) : ℝ) ≤ ((84241224989605725 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((336964899958422897 / 72057594037927936 : ℚ) : ℝ) ≤ ((859 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((859 / 8 : ℚ) : ℝ) ≤ Real.exp ((84241224989605725 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_63 : heightPower (63 : Fin 125) ≤ ((2266247186861055 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_63
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_63 : heightFactor (63 : Fin 125) ≤ ((99198211676265 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_63
  obtain ⟨hpl, hph⟩ := kernel_bounds_858
  obtain ⟨hcl, hch⟩ := kernel_bounds_859
  obtain ⟨hzl, hzh⟩ := height_z_bounds_859
  have h : (((737881 / 32 : ℚ) : ℝ) * (logKernel ((429 / 4 : ℚ) : ℝ) - logKernel ((859 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((859 / 8 : ℚ) : ℝ) + Real.log ((859 / 8 : ℚ) : ℝ) - ((104 / 1 : ℚ) : ℝ))) ≤ ((99198211676265 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

end LegendreK6.M3Far.Enclosures.Height001
