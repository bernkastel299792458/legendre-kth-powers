import LegendreK6.M2PilotDefinitions
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp

/-! Generated proposals: every bound is checked by Lean, not by trusting Arb. -/
namespace LegendreK6.M2Pilot.Enclosures.Height001
set_option maxRecDepth 100000
set_option maxHeartbeats 0

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

theorem height_z_bounds_1874 : ((2669962868775157877 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((937 / 32 : ℚ) : ℝ) ∧
    heightZ ((937 / 32 : ℚ) : ℝ) ≤ ((5339925737550315757 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((2669962868775157877 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((937 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((53 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((937 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((53 / 96 : ℚ) : ℝ) ≤ ((5339925737550315757 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1874 : ((10765979309577249 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((937 / 32 : ℚ) : ℝ) ∧
    logKernel ((937 / 32 : ℚ) : ℝ) ≤ ((43063917238309001 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1874
  constructor
  · exact (show ((10765979309577249 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((2669962868775157877 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((937 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((5339925737550315757 / 18446744073709551616 : ℚ) : ℝ) ≤ ((43063917238309001 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1875 : ((2628568931245881727 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((1875 / 64 : ℚ) : ℝ) ∧
    heightZ ((1875 / 64 : ℚ) : ℝ) ≤ ((5257137862491763457 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((2628568931245881727 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((1875 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((103 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((1875 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((103 / 192 : ℚ) : ℝ) ≤ ((5257137862491763457 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1875 : ((42396273084610993 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1875 / 64 : ℚ) : ℝ) ∧
    logKernel ((1875 / 64 : ℚ) : ℝ) ≤ ((21198136542305499 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1875
  constructor
  · exact (show ((42396273084610993 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((2628568931245881727 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1875 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((5257137862491763457 / 18446744073709551616 : ℚ) : ℝ) ≤ ((21198136542305499 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1876 : ((2587816747234684899 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((469 / 16 : ℚ) : ℝ) ∧
    heightZ ((469 / 16 : ℚ) : ℝ) ≤ ((5175633494469369801 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((2587816747234684899 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((469 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((25 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((469 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((25 / 48 : ℚ) : ℝ) ≤ ((5175633494469369801 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1876 : ((20869489897053909 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((469 / 16 : ℚ) : ℝ) ∧
    logKernel ((469 / 16 : ℚ) : ℝ) ≤ ((41738979794107823 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1876
  constructor
  · exact (show ((20869489897053909 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((2587816747234684899 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((469 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((5175633494469369801 / 18446744073709551616 : ℚ) : ℝ) ≤ ((41738979794107823 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1877 : ((5095392734550945699 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1877 / 64 : ℚ) : ℝ) ∧
    heightZ ((1877 / 64 : ℚ) : ℝ) ≤ ((2547696367275472851 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((5095392734550945699 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1877 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((97 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((1877 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((97 / 192 : ℚ) : ℝ) ≤ ((2547696367275472851 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1877 : ((20545938445769941 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((1877 / 64 : ℚ) : ℝ) ∧
    logKernel ((1877 / 64 : ℚ) : ℝ) ≤ ((41091876891539887 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1877
  constructor
  · exact (show ((20545938445769941 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((5095392734550945699 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1877 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((2547696367275472851 / 9223372036854775808 : ℚ) : ℝ) ≤ ((41091876891539887 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1878 : ((1254098998077162697 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((939 / 32 : ℚ) : ℝ) ∧
    heightZ ((939 / 32 : ℚ) : ℝ) ≤ ((5016395992308650791 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((1254098998077162697 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((939 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((47 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((939 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((47 / 96 : ℚ) : ℝ) ≤ ((5016395992308650791 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1878 : ((40454806389585891 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((939 / 32 : ℚ) : ℝ) ∧
    logKernel ((939 / 32 : ℚ) : ℝ) ≤ ((5056850798698237 / 9007199254740992 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1878
  constructor
  · exact (show ((40454806389585891 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((1254098998077162697 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((939 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((5016395992308650791 / 18446744073709551616 : ℚ) : ℝ) ≤ ((5056850798698237 / 9007199254740992 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1879 : ((4938623981036076811 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1879 / 64 : ℚ) : ℝ) ∧
    heightZ ((1879 / 64 : ℚ) : ℝ) ≤ ((2469311990518038407 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((4938623981036076811 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1879 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((91 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((1879 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((91 / 192 : ℚ) : ℝ) ≤ ((2469311990518038407 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1879 : ((9956903187572735 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((1879 / 64 : ℚ) : ℝ) ∧
    logKernel ((1879 / 64 : ℚ) : ℝ) ≤ ((39827612750290945 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1879
  constructor
  · exact (show ((9956903187572735 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((4938623981036076811 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1879 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((2469311990518038407 / 9223372036854775808 : ℚ) : ℝ) ≤ ((39827612750290945 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1880 : ((4862057713039483273 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((235 / 8 : ℚ) : ℝ) ∧
    heightZ ((235 / 8 : ℚ) : ℝ) ≤ ((1215514428259870819 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((4862057713039483273 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((235 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((11 / 24 : ℚ) : ℝ) ∧
      Real.exp (-((235 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((11 / 24 : ℚ) : ℝ) ≤ ((1215514428259870819 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1880 : ((39210142847092605 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((235 / 8 : ℚ) : ℝ) ∧
    logKernel ((235 / 8 : ℚ) : ℝ) ≤ ((19605071423546305 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1880
  constructor
  · exact (show ((39210142847092605 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((4862057713039483273 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((235 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1215514428259870819 / 4611686018427387904 : ℚ) : ℝ) ≤ ((19605071423546305 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1881 : ((598334811875254463 / 2305843009213693952 : ℚ) : ℝ) ≤ heightZ ((1881 / 64 : ℚ) : ℝ) ∧
    heightZ ((1881 / 64 : ℚ) : ℝ) ≤ ((4786678495002035707 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((598334811875254463 / 2305843009213693952 : ℚ) : ℝ) ≤ Real.exp (-((1881 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((85 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((1881 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((85 / 192 : ℚ) : ℝ) ≤ ((4786678495002035707 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1881 : ((38602245927435769 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1881 / 64 : ℚ) : ℝ) ∧
    logKernel ((1881 / 64 : ℚ) : ℝ) ≤ ((19301122963717887 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1881
  constructor
  · exact (show ((38602245927435769 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((598334811875254463 / 2305843009213693952 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1881 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((4786678495002035707 / 18446744073709551616 : ℚ) : ℝ) ≤ ((19301122963717887 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1882 : ((4712467923419914759 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((941 / 32 : ℚ) : ℝ) ∧
    heightZ ((941 / 32 : ℚ) : ℝ) ≤ ((2356233961709957381 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((4712467923419914759 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((941 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((41 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((941 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((41 / 96 : ℚ) : ℝ) ≤ ((2356233961709957381 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1882 : ((9500943393991763 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((941 / 32 : ℚ) : ℝ) ∧
    logKernel ((941 / 32 : ℚ) : ℝ) ≤ ((38003773575967057 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1882
  constructor
  · exact (show ((9500943393991763 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((4712467923419914759 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((941 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((2356233961709957381 / 9223372036854775808 : ℚ) : ℝ) ≤ ((38003773575967057 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1883 : ((4639407880109181875 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1883 / 64 : ℚ) : ℝ) ∧
    heightZ ((1883 / 64 : ℚ) : ℝ) ≤ ((2319703940054590939 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((4639407880109181875 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1883 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((79 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((1883 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((79 / 192 : ℚ) : ℝ) ≤ ((2319703940054590939 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1883 : ((37414579678299851 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1883 / 64 : ℚ) : ℝ) ∧
    logKernel ((1883 / 64 : ℚ) : ℝ) ≤ ((2338411229893741 / 4503599627370496 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1883
  constructor
  · exact (show ((37414579678299851 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((4639407880109181875 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1883 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((2319703940054590939 / 9223372036854775808 : ℚ) : ℝ) ≤ ((2338411229893741 / 4503599627370496 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1884 : ((285467532986394033 / 1152921504606846976 : ℚ) : ℝ) ≤ heightZ ((471 / 16 : ℚ) : ℝ) ∧
    heightZ ((471 / 16 : ℚ) : ℝ) ≤ ((4567480527782304531 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((285467532986394033 / 1152921504606846976 : ℚ) : ℝ) ≤ Real.exp (-((471 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((19 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((471 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((19 / 48 : ℚ) : ℝ) ≤ ((4567480527782304531 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1884 : ((36834520385341163 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((471 / 16 : ℚ) : ℝ) ∧
    logKernel ((471 / 16 : ℚ) : ℝ) ≤ ((2302157524083823 / 4503599627370496 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1884
  constructor
  · exact (show ((36834520385341163 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((285467532986394033 / 1152921504606846976 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((471 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((4567480527782304531 / 18446744073709551616 : ℚ) : ℝ) ≤ ((2302157524083823 / 4503599627370496 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1885 : ((4496668305693261109 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1885 / 64 : ℚ) : ℝ) ∧
    heightZ ((1885 / 64 : ℚ) : ℝ) ≤ ((562083538211657639 / 2305843009213693952 : ℚ) : ℝ) := by
  have h : ((4496668305693261109 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1885 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((73 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((1885 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((73 / 192 : ℚ) : ℝ) ≤ ((562083538211657639 / 2305843009213693952 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1885 : ((18131727039085729 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((1885 / 64 : ℚ) : ℝ) ∧
    logKernel ((1885 / 64 : ℚ) : ℝ) ≤ ((36263454078171463 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1885
  constructor
  · exact (show ((18131727039085729 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((4496668305693261109 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1885 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((562083538211657639 / 2305843009213693952 : ℚ) : ℝ) ≤ ((36263454078171463 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1886 : ((553369240668770273 / 2305843009213693952 : ℚ) : ℝ) ≤ heightZ ((943 / 32 : ℚ) : ℝ) ∧
    heightZ ((943 / 32 : ℚ) : ℝ) ≤ ((4426953925350162187 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((553369240668770273 / 2305843009213693952 : ℚ) : ℝ) ≤ Real.exp (-((943 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((35 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((943 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((35 / 96 : ℚ) : ℝ) ≤ ((4426953925350162187 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1886 : ((35701241333469047 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((943 / 32 : ℚ) : ℝ) ∧
    logKernel ((943 / 32 : ℚ) : ℝ) ≤ ((8925310333367263 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1886
  constructor
  · exact (show ((35701241333469047 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((553369240668770273 / 2305843009213693952 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((943 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((4426953925350162187 / 18446744073709551616 : ℚ) : ℝ) ≤ ((8925310333367263 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1887 : ((1089580091573585353 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((1887 / 64 : ℚ) : ℝ) ∧
    heightZ ((1887 / 64 : ℚ) : ℝ) ≤ ((4358320366294341415 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((1089580091573585353 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((1887 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((67 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((1887 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((67 / 192 : ℚ) : ℝ) ≤ ((4358320366294341415 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1887 : ((35147744889470493 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1887 / 64 : ℚ) : ℝ) ∧
    logKernel ((1887 / 64 : ℚ) : ℝ) ≤ ((17573872444735249 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1887
  constructor
  · exact (show ((35147744889470493 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((1089580091573585353 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1887 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((4358320366294341415 / 18446744073709551616 : ℚ) : ℝ) ≤ ((17573872444735249 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1888 : ((4290750871944885579 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((59 / 2 : ℚ) : ℝ) ∧
    heightZ ((59 / 2 : ℚ) : ℝ) ≤ ((2145375435972442791 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((4290750871944885579 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((59 / 2 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((1 / 3 : ℚ) : ℝ) ∧
      Real.exp (-((59 / 2 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((1 / 3 : ℚ) : ℝ) ≤ ((2145375435972442791 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1888 : ((135167303173667 / 281474976710656 : ℚ) : ℝ) ≤ logKernel ((59 / 2 : ℚ) : ℝ) ∧
    logKernel ((59 / 2 : ℚ) : ℝ) ≤ ((34602829612458757 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1888
  constructor
  · exact (show ((135167303173667 / 281474976710656 : ℚ) : ℝ) ≤ zKernel ((4290750871944885579 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((59 / 2 : ℚ) : ℝ)) hh).trans
      (show zKernel ((2145375435972442791 / 9223372036854775808 : ℚ) : ℝ) ≤ ((34602829612458757 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1889 : ((1056057236376897309 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((1889 / 64 : ℚ) : ℝ) ∧
    heightZ ((1889 / 64 : ℚ) : ℝ) ≤ ((4224228945507589239 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((1056057236376897309 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((1889 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((61 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((1889 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((61 / 192 : ℚ) : ℝ) ≤ ((4224228945507589239 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1889 : ((17033181231885439 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((1889 / 64 : ℚ) : ℝ) ∧
    logKernel ((1889 / 64 : ℚ) : ℝ) ≤ ((34066362463770883 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1889
  constructor
  · exact (show ((17033181231885439 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((1056057236376897309 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1889 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((4224228945507589239 / 18446744073709551616 : ℚ) : ℝ) ≤ ((34066362463770883 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1890 : ((64980286655427111 / 288230376151711744 : ℚ) : ℝ) ≤ heightZ ((945 / 32 : ℚ) : ℝ) ∧
    heightZ ((945 / 32 : ℚ) : ℝ) ≤ ((4158738345947335107 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((64980286655427111 / 288230376151711744 : ℚ) : ℝ) ≤ Real.exp (-((945 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((29 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((945 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((29 / 96 : ℚ) : ℝ) ≤ ((4158738345947335107 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1890 : ((1048069139603663 / 2251799813685248 : ℚ) : ℝ) ≤ logKernel ((945 / 32 : ℚ) : ℝ) ∧
    logKernel ((945 / 32 : ℚ) : ℝ) ≤ ((33538212467317221 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1890
  constructor
  · exact (show ((1048069139603663 / 2251799813685248 : ℚ) : ℝ) ≤ zKernel ((64980286655427111 / 288230376151711744 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((945 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((4158738345947335107 / 18446744073709551616 : ℚ) : ℝ) ≤ ((33538212467317221 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1891 : ((4094263084022916945 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1891 / 64 : ℚ) : ℝ) ∧
    heightZ ((1891 / 64 : ℚ) : ℝ) ≤ ((1023565771005729237 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((4094263084022916945 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1891 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((55 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((1891 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((55 / 192 : ℚ) : ℝ) ≤ ((1023565771005729237 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1891 : ((16509125338802083 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((1891 / 64 : ℚ) : ℝ) ∧
    logKernel ((1891 / 64 : ℚ) : ℝ) ≤ ((33018250677604171 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1891
  constructor
  · exact (show ((16509125338802083 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((4094263084022916945 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1891 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1023565771005729237 / 4611686018427387904 : ℚ) : ℝ) ≤ ((33018250677604171 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1892 : ((1007696854595834199 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((473 / 16 : ℚ) : ℝ) ∧
    heightZ ((473 / 16 : ℚ) : ℝ) ≤ ((4030787418383336799 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((1007696854595834199 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((473 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((13 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((473 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((13 / 48 : ℚ) : ℝ) ≤ ((4030787418383336799 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1892 : ((16253175074126357 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((473 / 16 : ℚ) : ℝ) ∧
    logKernel ((473 / 16 : ℚ) : ℝ) ≤ ((32506350148252719 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1892
  constructor
  · exact (show ((16253175074126357 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((1007696854595834199 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((473 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((4030787418383336799 / 18446744073709551616 : ℚ) : ℝ) ≤ ((32506350148252719 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1893 : ((1984147925862311755 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((1893 / 64 : ℚ) : ℝ) ∧
    heightZ ((1893 / 64 : ℚ) : ℝ) ≤ ((3968295851724623513 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((1984147925862311755 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((1893 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((49 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((1893 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((49 / 192 : ℚ) : ℝ) ≤ ((3968295851724623513 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1893 : ((16001192950502513 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((1893 / 64 : ℚ) : ℝ) ∧
    logKernel ((1893 / 64 : ℚ) : ℝ) ≤ ((32002385901005031 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1893
  constructor
  · exact (show ((16001192950502513 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((1984147925862311755 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1893 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((3968295851724623513 / 18446744073709551616 : ℚ) : ℝ) ≤ ((32002385901005031 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1894 : ((1953386563503117153 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((947 / 32 : ℚ) : ℝ) ∧
    heightZ ((947 / 32 : ℚ) : ℝ) ≤ ((3906773127006234309 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((1953386563503117153 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((947 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((23 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((947 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((23 / 96 : ℚ) : ℝ) ≤ ((3906773127006234309 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1894 : ((7876558723802891 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((947 / 32 : ℚ) : ℝ) ∧
    logKernel ((947 / 32 : ℚ) : ℝ) ≤ ((31506234895211569 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1894
  constructor
  · exact (show ((7876558723802891 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((1953386563503117153 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((947 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((3906773127006234309 / 18446744073709551616 : ℚ) : ℝ) ≤ ((31506234895211569 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1895 : ((1923102111863057783 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((1895 / 64 : ℚ) : ℝ) ∧
    heightZ ((1895 / 64 : ℚ) : ℝ) ≤ ((3846204223726115569 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((1923102111863057783 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((1895 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((43 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((1895 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((43 / 192 : ℚ) : ℝ) ≤ ((3846204223726115569 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1895 : ((7754443999447813 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((1895 / 64 : ℚ) : ℝ) ∧
    logKernel ((1895 / 64 : ℚ) : ℝ) ≤ ((31017775997791257 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1895
  constructor
  · exact (show ((7754443999447813 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((1923102111863057783 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1895 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((3846204223726115569 / 18446744073709551616 : ℚ) : ℝ) ≤ ((31017775997791257 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1896 : ((3786574354253513473 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((237 / 8 : ℚ) : ℝ) ∧
    heightZ ((237 / 8 : ℚ) : ℝ) ≤ ((946643588563378369 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((3786574354253513473 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((237 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((5 / 24 : ℚ) : ℝ) ∧
      Real.exp (-((237 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((5 / 24 : ℚ) : ℝ) ≤ ((946643588563378369 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1896 : ((7634222488414341 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((237 / 8 : ℚ) : ℝ) ∧
    logKernel ((237 / 8 : ℚ) : ℝ) ≤ ((30536889953657369 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1896
  constructor
  · exact (show ((7634222488414341 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((3786574354253513473 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((237 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((946643588563378369 / 4611686018427387904 : ℚ) : ℝ) ≤ ((30536889953657369 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1897 : ((931967240054659785 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((1897 / 64 : ℚ) : ℝ) ∧
    heightZ ((1897 / 64 : ℚ) : ℝ) ≤ ((3727868960218639143 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((931967240054659785 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((1897 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((37 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((1897 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((37 / 192 : ℚ) : ℝ) ≤ ((3727868960218639143 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1897 : ((15031729678300963 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((1897 / 64 : ℚ) : ℝ) ∧
    logKernel ((1897 / 64 : ℚ) : ℝ) ≤ ((30063459356601931 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1897
  constructor
  · exact (show ((15031729678300963 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((931967240054659785 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1897 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((3727868960218639143 / 18446744073709551616 : ℚ) : ℝ) ≤ ((30063459356601931 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1898 : ((3670073708958306803 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((949 / 32 : ℚ) : ℝ) ∧
    heightZ ((949 / 32 : ℚ) : ℝ) ≤ ((1835036854479153403 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((3670073708958306803 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((949 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((17 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((949 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((17 / 96 : ℚ) : ℝ) ≤ ((1835036854479153403 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1898 : ((1849835538789469 / 4503599627370496 : ℚ) : ℝ) ≤ logKernel ((949 / 32 : ℚ) : ℝ) ∧
    logKernel ((949 / 32 : ℚ) : ℝ) ≤ ((29597368620631509 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1898
  constructor
  · exact (show ((1849835538789469 / 4503599627370496 : ℚ) : ℝ) ≤ zKernel ((3670073708958306803 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((949 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1835036854479153403 / 9223372036854775808 : ℚ) : ℝ) ≤ ((29597368620631509 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1899 : ((1806587245008338639 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((1899 / 64 : ℚ) : ℝ) ∧
    heightZ ((1899 / 64 : ℚ) : ℝ) ≤ ((3613174490016677281 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((1806587245008338639 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((1899 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((31 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((1899 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((31 / 192 : ℚ) : ℝ) ≤ ((3613174490016677281 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1899 : ((29138503951747395 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1899 / 64 : ℚ) : ℝ) ∧
    logKernel ((1899 / 64 : ℚ) : ℝ) ≤ ((3642312993968425 / 9007199254740992 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1899
  constructor
  · exact (show ((29138503951747395 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((1806587245008338639 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1899 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((3613174490016677281 / 18446744073709551616 : ℚ) : ℝ) ≤ ((3642312993968425 / 9007199254740992 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1900 : ((3557157411700252365 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((475 / 16 : ℚ) : ℝ) ∧
    heightZ ((475 / 16 : ℚ) : ℝ) ≤ ((222322338231265773 / 1152921504606846976 : ℚ) : ℝ) := by
  have h : ((3557157411700252365 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((475 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((7 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((475 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((7 / 48 : ℚ) : ℝ) ≤ ((222322338231265773 / 1152921504606846976 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1900 : ((28686753320163323 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((475 / 16 : ℚ) : ℝ) ∧
    logKernel ((475 / 16 : ℚ) : ℝ) ≤ ((14007203769611 / 35184372088832 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1900
  constructor
  · exact (show ((28686753320163323 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((3557157411700252365 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((475 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((222322338231265773 / 1152921504606846976 : ℚ) : ℝ) ≤ ((14007203769611 / 35184372088832 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1901 : ((3502008797686279117 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1901 / 64 : ℚ) : ℝ) ∧
    heightZ ((1901 / 64 : ℚ) : ℝ) ≤ ((218875549855392445 / 1152921504606846976 : ℚ) : ℝ) := by
  have h : ((3502008797686279117 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1901 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((25 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((1901 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((25 / 192 : ℚ) : ℝ) ≤ ((218875549855392445 / 1152921504606846976 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1901 : ((28242006432953861 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1901 / 64 : ℚ) : ℝ) ∧
    logKernel ((1901 / 64 : ℚ) : ℝ) ≤ ((14121003216476933 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1901
  constructor
  · exact (show ((28242006432953861 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((3502008797686279117 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1901 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((218875549855392445 / 1152921504606846976 : ℚ) : ℝ) ≤ ((14121003216476933 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1902 : ((215482198980233495 / 1152921504606846976 : ℚ) : ℝ) ≤ heightZ ((951 / 32 : ℚ) : ℝ) ∧
    heightZ ((951 / 32 : ℚ) : ℝ) ≤ ((3447715183683735923 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((215482198980233495 / 1152921504606846976 : ℚ) : ℝ) ≤ Real.exp (-((951 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((11 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((951 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((11 / 96 : ℚ) : ℝ) ≤ ((3447715183683735923 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1902 : ((6951038676781725 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((951 / 32 : ℚ) : ℝ) ∧
    logKernel ((951 / 32 : ℚ) : ℝ) ≤ ((27804154707126905 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1902
  constructor
  · exact (show ((6951038676781725 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((215482198980233495 / 1152921504606846976 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((951 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((3447715183683735923 / 18446744073709551616 : ℚ) : ℝ) ≤ ((27804154707126905 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1903 : ((3394263314146085191 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1903 / 64 : ℚ) : ℝ) ∧
    heightZ ((1903 / 64 : ℚ) : ℝ) ≤ ((1697131657073042597 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((3394263314146085191 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1903 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((19 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((1903 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((19 / 192 : ℚ) : ℝ) ≤ ((1697131657073042597 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1903 : ((6843272810778397 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((1903 / 64 : ℚ) : ℝ) ∧
    logKernel ((1903 / 64 : ℚ) : ℝ) ≤ ((27373091243113593 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1903
  constructor
  · exact (show ((6843272810778397 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((3394263314146085191 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1903 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1697131657073042597 / 9223372036854775808 : ℚ) : ℝ) ≤ ((27373091243113593 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1904 : ((1670820069517495061 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((119 / 4 : ℚ) : ℝ) ∧
    heightZ ((119 / 4 : ℚ) : ℝ) ≤ ((3341640139034990125 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((1670820069517495061 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((119 / 4 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((1 / 12 : ℚ) : ℝ) ∧
      Real.exp (-((119 / 4 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((1 / 12 : ℚ) : ℝ) ≤ ((3341640139034990125 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1904 : ((26948710798669273 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((119 / 4 : ℚ) : ℝ) ∧
    logKernel ((119 / 4 : ℚ) : ℝ) ≤ ((13474355399334639 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1904
  constructor
  · exact (show ((26948710798669273 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((1670820069517495061 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((119 / 4 : ℚ) : ℝ)) hh).trans
      (show zKernel ((3341640139034990125 / 18446744073709551616 : ℚ) : ℝ) ≤ ((13474355399334639 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1905 : ((822458202658551335 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((1905 / 64 : ℚ) : ℝ) ∧
    heightZ ((1905 / 64 : ℚ) : ℝ) ≤ ((3289832810634205343 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((822458202658551335 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((1905 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((13 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((1905 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((13 / 192 : ℚ) : ℝ) ≤ ((3289832810634205343 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1905 : ((26530909763179073 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1905 / 64 : ℚ) : ℝ) ∧
    logKernel ((1905 / 64 : ℚ) : ℝ) ≤ ((13265454881589539 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1905
  constructor
  · exact (show ((26530909763179073 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((822458202658551335 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1905 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((3289832810634205343 / 18446744073709551616 : ℚ) : ℝ) ≤ ((13265454881589539 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem log_height_bounds_32 : ((243334703355038121 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((937 / 32 : ℚ) : ℝ) ∧
    Real.log ((937 / 32 : ℚ) : ℝ) ≤ ((60833675838759531 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((243334703355038121 / 72057594037927936 : ℚ) : ℝ) ≤ ((937 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((937 / 32 : ℚ) : ℝ) ≤ Real.exp ((60833675838759531 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_32 : heightPower (32 : Fin 988) ≤ ((145683673448587 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_32
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_32 : heightFactor (32 : Fin 988) ≤ ((1349479967396157 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_32
  obtain ⟨hpl, hph⟩ := kernel_bounds_1873
  obtain ⟨hcl, hch⟩ := kernel_bounds_1874
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1874
  have h : (((877969 / 512 : ℚ) : ℝ) * (logKernel ((1873 / 64 : ℚ) : ℝ) - logKernel ((937 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((937 / 32 : ℚ) : ℝ) + Real.log ((937 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1349479967396157 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_33 : ((243373144323694761 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1875 / 64 : ℚ) : ℝ) ∧
    Real.log ((1875 / 64 : ℚ) : ℝ) ≤ ((60843286080923691 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((243373144323694761 / 72057594037927936 : ℚ) : ℝ) ≤ ((1875 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1875 / 64 : ℚ) : ℝ) ≤ Real.exp ((60843286080923691 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_33 : heightPower (33 : Fin 988) ≤ ((75115939996753 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_33
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_33 : heightFactor (33 : Fin 988) ≤ ((2674318547269489 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_33
  obtain ⟨hpl, hph⟩ := kernel_bounds_1874
  obtain ⟨hcl, hch⟩ := kernel_bounds_1875
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1875
  have h : (((3515625 / 2048 : ℚ) : ℝ) * (logKernel ((937 / 32 : ℚ) : ℝ) - logKernel ((1875 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1875 / 64 : ℚ) : ℝ) + Real.log ((1875 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((2674318547269489 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_34 : ((243411564795966181 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((469 / 16 : ℚ) : ℝ) ∧
    Real.log ((469 / 16 : ℚ) : ℝ) ≤ ((30426445599495773 / 9007199254740992 : ℚ) : ℝ) := by
  have hl : Real.exp ((243411564795966181 / 72057594037927936 : ℚ) : ℝ) ≤ ((469 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((469 / 16 : ℚ) : ℝ) ≤ Real.exp ((30426445599495773 / 9007199254740992 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_34 : heightPower (34 : Fin 988) ≤ ((38695001618605 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_34
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_34 : heightFactor (34 : Fin 988) ≤ ((5299800751599845 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_34
  obtain ⟨hpl, hph⟩ := kernel_bounds_1875
  obtain ⟨hcl, hch⟩ := kernel_bounds_1876
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1876
  have h : (((219961 / 128 : ℚ) : ℝ) * (logKernel ((1875 / 64 : ℚ) : ℝ) - logKernel ((469 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((469 / 16 : ℚ) : ℝ) + Real.log ((469 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((5299800751599845 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_35 : ((243449964793697719 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1877 / 64 : ℚ) : ℝ) ∧
    Real.log ((1877 / 64 : ℚ) : ℝ) ≤ ((121724982396848861 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((243449964793697719 / 72057594037927936 : ℚ) : ℝ) ≤ ((1877 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1877 / 64 : ℚ) : ℝ) ≤ Real.exp ((121724982396848861 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_35 : heightPower (35 : Fin 988) ≤ ((159328052976663 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_35
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_35 : heightFactor (35 : Fin 988) ≤ ((2625703416406165 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_35
  obtain ⟨hpl, hph⟩ := kernel_bounds_1876
  obtain ⟨hcl, hch⟩ := kernel_bounds_1877
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1877
  have h : (((3523129 / 2048 : ℚ) : ℝ) * (logKernel ((469 / 16 : ℚ) : ℝ) - logKernel ((1877 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1877 / 64 : ℚ) : ℝ) + Real.log ((1877 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((2625703416406165 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_36 : ((60872086084674951 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((939 / 32 : ℚ) : ℝ) ∧
    Real.log ((939 / 32 : ℚ) : ℝ) ≤ ((243488344338699807 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((60872086084674951 / 18014398509481984 : ℚ) : ℝ) ≤ ((939 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((939 / 32 : ℚ) : ℝ) ≤ Real.exp ((243488344338699807 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_36 : heightPower (36 : Fin 988) ≤ ((20484502448179 / 35184372088832 : ℚ) : ℝ) := by
  have hh := log_height_bounds_36
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_36 : heightFactor (36 : Fin 988) ≤ ((5203451365833405 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_36
  obtain ⟨hpl, hph⟩ := kernel_bounds_1877
  obtain ⟨hcl, hch⟩ := kernel_bounds_1878
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1878
  have h : (((881721 / 512 : ℚ) : ℝ) * (logKernel ((1877 / 64 : ℚ) : ℝ) - logKernel ((939 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((939 / 32 : ℚ) : ℝ) + Real.log ((939 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((5203451365833405 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_37 : ((121763351726374017 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((1879 / 64 : ℚ) : ℝ) ∧
    Real.log ((1879 / 64 : ℚ) : ℝ) ≤ ((243526703452748037 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((121763351726374017 / 36028797018963968 : ℚ) : ℝ) ≤ ((1879 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1879 / 64 : ℚ) : ℝ) ≤ Real.exp ((243526703452748037 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_37 : heightPower (37 : Fin 988) ≤ ((168423906385787 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_37
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_37 : heightFactor (37 : Fin 988) ≤ ((2577965206809647 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_37
  obtain ⟨hpl, hph⟩ := kernel_bounds_1878
  obtain ⟨hcl, hch⟩ := kernel_bounds_1879
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1879
  have h : (((3530641 / 2048 : ℚ) : ℝ) * (logKernel ((939 / 32 : ℚ) : ℝ) - logKernel ((1879 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1879 / 64 : ℚ) : ℝ) + Real.log ((1879 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((2577965206809647 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_38 : ((243565042157583251 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((235 / 8 : ℚ) : ℝ) ∧
    Real.log ((235 / 8 : ℚ) : ℝ) ≤ ((121782521078791627 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((243565042157583251 / 72057594037927936 : ℚ) : ℝ) ≤ ((235 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((235 / 8 : ℚ) : ℝ) ≤ Real.exp ((121782521078791627 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_38 : heightPower (38 : Fin 988) ≤ ((172971713462653 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_38
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_38 : heightFactor (38 : Fin 988) ≤ ((1277210018528893 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_38
  obtain ⟨hpl, hph⟩ := kernel_bounds_1879
  obtain ⟨hcl, hch⟩ := kernel_bounds_1880
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1880
  have h : (((55225 / 32 : ℚ) : ℝ) * (logKernel ((1879 / 64 : ℚ) : ℝ) - logKernel ((235 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((235 / 8 : ℚ) : ℝ) + Real.log ((235 / 8 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1277210018528893 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_39 : ((243603360474911613 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1881 / 64 : ℚ) : ℝ) ∧
    Real.log ((1881 / 64 : ℚ) : ℝ) ≤ ((1903151253710247 / 562949953421312 : ℚ) : ℝ) := by
  have hl : Real.exp ((243603360474911613 / 72057594037927936 : ℚ) : ℝ) ≤ ((1881 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1881 / 64 : ℚ) : ℝ) ≤ Real.exp ((1903151253710247 / 562949953421312 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_39 : heightPower (39 : Fin 988) ≤ ((177519440900821 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_39
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_39 : heightFactor (39 : Fin 988) ≤ ((2531088239974967 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_39
  obtain ⟨hpl, hph⟩ := kernel_bounds_1880
  obtain ⟨hcl, hch⟩ := kernel_bounds_1881
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1881
  have h : (((3538161 / 2048 : ℚ) : ℝ) * (logKernel ((235 / 8 : ℚ) : ℝ) - logKernel ((1881 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1881 / 64 : ℚ) : ℝ) + Real.log ((1881 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((2531088239974967 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_40 : ((243641658426404665 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((941 / 32 : ℚ) : ℝ) ∧
    Real.log ((941 / 32 : ℚ) : ℝ) ≤ ((60910414606601167 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((243641658426404665 / 72057594037927936 : ℚ) : ℝ) ≤ ((941 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((941 / 32 : ℚ) : ℝ) ≤ Real.exp ((60910414606601167 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_40 : heightPower (40 : Fin 988) ≤ ((182067088784945 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_40
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_40 : heightFactor (40 : Fin 988) ≤ ((2507967899063817 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_40
  obtain ⟨hpl, hph⟩ := kernel_bounds_1881
  obtain ⟨hcl, hch⟩ := kernel_bounds_1882
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1882
  have h : (((885481 / 512 : ℚ) : ℝ) * (logKernel ((1881 / 64 : ℚ) : ℝ) - logKernel ((941 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((941 / 32 : ℚ) : ℝ) + Real.log ((941 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((2507967899063817 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_41 : ((243679936033699421 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1883 / 64 : ℚ) : ℝ) ∧
    Real.log ((1883 / 64 : ℚ) : ℝ) ≤ ((7614998001053107 / 2251799813685248 : ℚ) : ℝ) := by
  have hl : Real.exp ((243679936033699421 / 72057594037927936 : ℚ) : ℝ) ≤ ((1883 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1883 / 64 : ℚ) : ℝ) ≤ Real.exp ((7614998001053107 / 2251799813685248 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_41 : heightPower (41 : Fin 988) ≤ ((23326832149943 / 35184372088832 : ℚ) : ℝ) := by
  have hh := log_height_bounds_41
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_41 : heightFactor (41 : Fin 988) ≤ ((2485057114864775 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_41
  obtain ⟨hpl, hph⟩ := kernel_bounds_1882
  obtain ⟨hcl, hch⟩ := kernel_bounds_1883
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1883
  have h : (((3545689 / 2048 : ℚ) : ℝ) * (logKernel ((941 / 32 : ℚ) : ℝ) - logKernel ((1883 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1883 / 64 : ℚ) : ℝ) + Real.log ((1883 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((2485057114864775 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_42 : ((243718193318398427 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((471 / 16 : ℚ) : ℝ) ∧
    Real.log ((471 / 16 : ℚ) : ℝ) ≤ ((121859096659199215 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((243718193318398427 / 72057594037927936 : ℚ) : ℝ) ≤ ((471 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((471 / 16 : ℚ) : ℝ) ≤ Real.exp ((121859096659199215 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_42 : heightPower (42 : Fin 988) ≤ ((191162146229003 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_42
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_42 : heightFactor (42 : Fin 988) ≤ ((4924708009612869 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_42
  obtain ⟨hpl, hph⟩ := kernel_bounds_1883
  obtain ⟨hcl, hch⟩ := kernel_bounds_1884
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1884
  have h : (((221841 / 128 : ℚ) : ℝ) * (logKernel ((1883 / 64 : ℚ) : ℝ) - logKernel ((471 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((471 / 16 : ℚ) : ℝ) + Real.log ((471 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((4924708009612869 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_43 : ((243756430302069843 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1885 / 64 : ℚ) : ℝ) ∧
    Real.log ((1885 / 64 : ℚ) : ℝ) ≤ ((121878215151034923 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((243756430302069843 / 72057594037927936 : ℚ) : ℝ) ≤ ((1885 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1885 / 64 : ℚ) : ℝ) ≤ Real.exp ((121878215151034923 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_43 : heightPower (43 : Fin 988) ≤ ((97854777978787 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_43
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_43 : heightFactor (43 : Fin 988) ≤ ((2439856703057183 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_43
  obtain ⟨hpl, hph⟩ := kernel_bounds_1884
  obtain ⟨hcl, hch⟩ := kernel_bounds_1885
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1885
  have h : (((3553225 / 2048 : ℚ) : ℝ) * (logKernel ((471 / 16 : ℚ) : ℝ) - logKernel ((1885 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1885 / 64 : ℚ) : ℝ) + Real.log ((1885 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((2439856703057183 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_44 : ((243794647006247509 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((943 / 32 : ℚ) : ℝ) ∧
    Real.log ((943 / 32 : ℚ) : ℝ) ≤ ((30474330875780939 / 9007199254740992 : ℚ) : ℝ) := by
  have hl : Real.exp ((243794647006247509 / 72057594037927936 : ℚ) : ℝ) ≤ ((943 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((943 / 32 : ℚ) : ℝ) ≤ Real.exp ((30474330875780939 / 9007199254740992 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_44 : heightPower (44 : Fin 988) ≤ ((50064221617343 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_44
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_44 : heightFactor (44 : Fin 988) ≤ ((4835126720756247 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_44
  obtain ⟨hpl, hph⟩ := kernel_bounds_1885
  obtain ⟨hcl, hch⟩ := kernel_bounds_1886
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1886
  have h : (((889249 / 512 : ℚ) : ℝ) * (logKernel ((1885 / 64 : ℚ) : ℝ) - logKernel ((943 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((943 / 32 : ℚ) : ℝ) + Real.log ((943 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((4835126720756247 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_45 : ((243832843452431023 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1887 / 64 : ℚ) : ℝ) ∧
    Real.log ((1887 / 64 : ℚ) : ℝ) ≤ ((121916421726215513 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((243832843452431023 / 72057594037927936 : ℚ) : ℝ) ≤ ((1887 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1887 / 64 : ℚ) : ℝ) ≤ Real.exp ((121916421726215513 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_45 : heightPower (45 : Fin 988) ≤ ((51201034462095 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_45
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_45 : heightFactor (45 : Fin 988) ≤ ((299434017997159 / 17592186044416 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_45
  obtain ⟨hpl, hph⟩ := kernel_bounds_1886
  obtain ⟨hcl, hch⟩ := kernel_bounds_1887
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1887
  have h : (((3560769 / 2048 : ℚ) : ℝ) * (logKernel ((943 / 32 : ℚ) : ℝ) - logKernel ((1887 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1887 / 64 : ℚ) : ℝ) + Real.log ((1887 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((299434017997159 / 17592186044416 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_46 : ((121935509831042905 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((59 / 2 : ℚ) : ℝ) ∧
    Real.log ((59 / 2 : ℚ) : ℝ) ≤ ((243871019662085813 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((121935509831042905 / 36028797018963968 : ℚ) : ℝ) ≤ ((59 / 2 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((59 / 2 : ℚ) : ℝ) ≤ Real.exp ((243871019662085813 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_46 : heightPower (46 : Fin 988) ≤ ((13084456886153 / 17592186044416 : ℚ) : ℝ) := by
  have hh := log_height_bounds_46
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_46 : heightFactor (46 : Fin 988) ≤ ((1186790618682509 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_46
  obtain ⟨hpl, hph⟩ := kernel_bounds_1887
  obtain ⟨hcl, hch⟩ := kernel_bounds_1888
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1888
  have h : (((3481 / 2 : ℚ) : ℝ) * (logKernel ((1887 / 64 : ℚ) : ℝ) - logKernel ((59 / 2 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((59 / 2 : ℚ) : ℝ) + Real.log ((59 / 2 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1186790618682509 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_47 : ((243909175656643199 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1889 / 64 : ℚ) : ℝ) ∧
    Real.log ((1889 / 64 : ℚ) : ℝ) ≤ ((121954587828321601 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((243909175656643199 / 72057594037927936 : ℚ) : ℝ) ≤ ((1889 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1889 / 64 : ℚ) : ℝ) ≤ Real.exp ((121954587828321601 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_47 : heightPower (47 : Fin 988) ≤ ((53474600885823 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_47
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_47 : heightFactor (47 : Fin 988) ≤ ((4703777680421671 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_47
  obtain ⟨hpl, hph⟩ := kernel_bounds_1888
  obtain ⟨hcl, hch⟩ := kernel_bounds_1889
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1889
  have h : (((3568321 / 2048 : ℚ) : ℝ) * (logKernel ((59 / 2 : ℚ) : ℝ) - logKernel ((1889 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1889 / 64 : ℚ) : ℝ) + Real.log ((1889 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((4703777680421671 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_48 : ((121973655728750243 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((945 / 32 : ℚ) : ℝ) ∧
    Real.log ((945 / 32 : ℚ) : ℝ) ≤ ((243947311457500489 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((121973655728750243 / 36028797018963968 : ℚ) : ℝ) ≤ ((945 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((945 / 32 : ℚ) : ℝ) ≤ Real.exp ((243947311457500489 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_48 : heightPower (48 : Fin 988) ≤ ((218445418026495 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_48
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_48 : heightFactor (48 : Fin 988) ≤ ((4660786336402475 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_48
  obtain ⟨hpl, hph⟩ := kernel_bounds_1889
  obtain ⟨hcl, hch⟩ := kernel_bounds_1890
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1890
  have h : (((893025 / 512 : ℚ) : ℝ) * (logKernel ((1889 / 64 : ℚ) : ℝ) - logKernel ((945 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((945 / 32 : ℚ) : ℝ) + Real.log ((945 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((4660786336402475 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_49 : ((243985427086021019 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1891 / 64 : ℚ) : ℝ) ∧
    Real.log ((1891 / 64 : ℚ) : ℝ) ≤ ((121992713543010511 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((243985427086021019 / 72057594037927936 : ℚ) : ℝ) ≤ ((1891 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1891 / 64 : ℚ) : ℝ) ≤ Real.exp ((121992713543010511 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_49 : heightPower (49 : Fin 988) ≤ ((222992353711507 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_49
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_49 : heightFactor (49 : Fin 988) ≤ ((4618184905797927 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_49
  obtain ⟨hpl, hph⟩ := kernel_bounds_1890
  obtain ⟨hcl, hch⟩ := kernel_bounds_1891
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1891
  have h : (((3575881 / 2048 : ℚ) : ℝ) * (logKernel ((945 / 32 : ℚ) : ℝ) - logKernel ((1891 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1891 / 64 : ℚ) : ℝ) + Real.log ((1891 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((4618184905797927 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_50 : ((122011761281767129 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((473 / 16 : ℚ) : ℝ) ∧
    Real.log ((473 / 16 : ℚ) : ℝ) ≤ ((244023522563534261 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((122011761281767129 / 36028797018963968 : ℚ) : ℝ) ≤ ((473 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((473 / 16 : ℚ) : ℝ) ≤ Real.exp ((244023522563534261 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_50 : heightPower (50 : Fin 988) ≤ ((227539210681647 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_50
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_50 : heightFactor (50 : Fin 988) ≤ ((4575969883206763 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_50
  obtain ⟨hpl, hph⟩ := kernel_bounds_1891
  obtain ⟨hcl, hch⟩ := kernel_bounds_1892
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1892
  have h : (((223729 / 128 : ℚ) : ℝ) * (logKernel ((1891 / 64 : ℚ) : ℝ) - logKernel ((473 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((473 / 16 : ℚ) : ℝ) + Real.log ((473 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((4575969883206763 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_51 : ((61015399477833963 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((1893 / 64 : ℚ) : ℝ) ∧
    Real.log ((1893 / 64 : ℚ) : ℝ) ≤ ((244061597911335855 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((61015399477833963 / 18014398509481984 : ℚ) : ℝ) ≤ ((1893 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1893 / 64 : ℚ) : ℝ) ≤ Real.exp ((244061597911335855 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_51 : heightPower (51 : Fin 988) ≤ ((232085989020101 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_51
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_51 : heightFactor (51 : Fin 988) ≤ ((2267068897212107 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_51
  obtain ⟨hpl, hph⟩ := kernel_bounds_1892
  obtain ⟨hcl, hch⟩ := kernel_bounds_1893
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1893
  have h : (((3583449 / 2048 : ℚ) : ℝ) * (logKernel ((473 / 16 : ℚ) : ℝ) - logKernel ((1893 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1893 / 64 : ℚ) : ℝ) + Real.log ((1893 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((2267068897212107 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_52 : ((7628114160958991 / 2251799813685248 : ℚ) : ℝ) ≤ Real.log ((947 / 32 : ℚ) : ℝ) ∧
    Real.log ((947 / 32 : ℚ) : ℝ) ≤ ((244099653150687715 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((7628114160958991 / 2251799813685248 : ℚ) : ℝ) ≤ ((947 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((947 / 32 : ℚ) : ℝ) ≤ Real.exp ((244099653150687715 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_52 : heightPower (52 : Fin 988) ≤ ((236632688809923 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_52
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_52 : heightFactor (52 : Fin 988) ≤ ((4492685196167635 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_52
  obtain ⟨hpl, hph⟩ := kernel_bounds_1893
  obtain ⟨hcl, hch⟩ := kernel_bounds_1894
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1894
  have h : (((896809 / 512 : ℚ) : ℝ) * (logKernel ((1893 / 64 : ℚ) : ℝ) - logKernel ((947 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((947 / 32 : ℚ) : ℝ) + Real.log ((947 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((4492685196167635 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_53 : ((244137688302818079 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1895 / 64 : ℚ) : ℝ) ∧
    Real.log ((1895 / 64 : ℚ) : ℝ) ≤ ((122068844151409041 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((244137688302818079 / 72057594037927936 : ℚ) : ℝ) ≤ ((1895 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1895 / 64 : ℚ) : ℝ) ≤ Real.exp ((122068844151409041 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_53 : heightPower (53 : Fin 988) ≤ ((241179310134037 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_53
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_53 : heightFactor (53 : Fin 988) ≤ ((4451608675804521 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_53
  obtain ⟨hpl, hph⟩ := kernel_bounds_1894
  obtain ⟨hcl, hch⟩ := kernel_bounds_1895
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1895
  have h : (((3591025 / 2048 : ℚ) : ℝ) * (logKernel ((947 / 32 : ℚ) : ℝ) - logKernel ((1895 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1895 / 64 : ℚ) : ℝ) + Real.log ((1895 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((4451608675804521 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_54 : ((244175703388921595 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((237 / 8 : ℚ) : ℝ) ∧
    Real.log ((237 / 8 : ℚ) : ℝ) ≤ ((122087851694460799 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((244175703388921595 / 72057594037927936 : ℚ) : ℝ) ≤ ((237 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((237 / 8 : ℚ) : ℝ) ≤ Real.exp ((122087851694460799 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_54 : heightPower (54 : Fin 988) ≤ ((7678932908601 / 8796093022208 : ℚ) : ℝ) := by
  have hh := log_height_bounds_54
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_54 : heightFactor (54 : Fin 988) ≤ ((4410904851082869 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_54
  obtain ⟨hpl, hph⟩ := kernel_bounds_1895
  obtain ⟨hcl, hch⟩ := kernel_bounds_1896
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1896
  have h : (((56169 / 32 : ℚ) : ℝ) * (logKernel ((1895 / 64 : ℚ) : ℝ) - logKernel ((237 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((237 / 8 : ℚ) : ℝ) + Real.log ((237 / 8 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((4410904851082869 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_55 : ((15263356151884961 / 4503599627370496 : ℚ) : ℝ) ≤ Real.log ((1897 / 64 : ℚ) : ℝ) ∧
    Real.log ((1897 / 64 : ℚ) : ℝ) ≤ ((244213698430159379 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((15263356151884961 / 4503599627370496 : ℚ) : ℝ) ≤ ((1897 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1897 / 64 : ℚ) : ℝ) ≤ Real.exp ((244213698430159379 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_55 : heightPower (55 : Fin 988) ≤ ((62568079429043 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_55
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_55 : heightFactor (55 : Fin 988) ≤ ((4370570369863897 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_55
  obtain ⟨hpl, hph⟩ := kernel_bounds_1896
  obtain ⟨hcl, hch⟩ := kernel_bounds_1897
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1897
  have h : (((3598609 / 2048 : ℚ) : ℝ) * (logKernel ((237 / 8 : ℚ) : ℝ) - logKernel ((1897 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1897 / 64 : ℚ) : ℝ) + Real.log ((1897 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((4370570369863897 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_56 : ((244251673447659083 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((949 / 32 : ℚ) : ℝ) ∧
    Real.log ((949 / 32 : ℚ) : ℝ) ≤ ((122125836723829543 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((244251673447659083 / 72057594037927936 : ℚ) : ℝ) ≤ ((949 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((949 / 32 : ℚ) : ℝ) ≤ Real.exp ((122125836723829543 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_56 : heightPower (56 : Fin 988) ≤ ((31852338017423 / 35184372088832 : ℚ) : ℝ) := by
  have hh := log_height_bounds_56
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_56 : heightFactor (56 : Fin 988) ≤ ((4330601909857065 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_56
  obtain ⟨hpl, hph⟩ := kernel_bounds_1897
  obtain ⟨hcl, hch⟩ := kernel_bounds_1898
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1898
  have h : (((900601 / 512 : ℚ) : ℝ) * (logKernel ((1897 / 64 : ℚ) : ℝ) - logKernel ((949 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((949 / 32 : ℚ) : ℝ) + Real.log ((949 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((4330601909857065 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_57 : ((61072407115628747 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((1899 / 64 : ℚ) : ℝ) ∧
    Real.log ((1899 / 64 : ℚ) : ℝ) ≤ ((244289628462514991 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((61072407115628747 / 18014398509481984 : ℚ) : ℝ) ≤ ((1899 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1899 / 64 : ℚ) : ℝ) ≤ Real.exp ((244289628462514991 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_57 : heightPower (57 : Fin 988) ≤ ((259365012427269 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_57
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_57 : heightFactor (57 : Fin 988) ≤ ((4290996178357407 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_57
  obtain ⟨hpl, hph⟩ := kernel_bounds_1898
  obtain ⟨hcl, hch⟩ := kernel_bounds_1899
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1899
  have h : (((3606201 / 2048 : ℚ) : ℝ) * (logKernel ((949 / 32 : ℚ) : ℝ) - logKernel ((1899 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1899 / 64 : ℚ) : ℝ) + Real.log ((1899 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((4290996178357407 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_58 : ((244327563495788051 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((475 / 16 : ℚ) : ℝ) ∧
    Real.log ((475 / 16 : ℚ) : ℝ) ≤ ((122163781747894027 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((244327563495788051 / 72057594037927936 : ℚ) : ℝ) ≤ ((475 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((475 / 16 : ℚ) : ℝ) ≤ Real.exp ((122163781747894027 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_58 : heightPower (58 : Fin 988) ≤ ((16494452666381 / 17592186044416 : ℚ) : ℝ) := by
  have hh := log_height_bounds_58
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_58 : heightFactor (58 : Fin 988) ≤ ((4251749911985137 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_58
  obtain ⟨hpl, hph⟩ := kernel_bounds_1899
  obtain ⟨hcl, hch⟩ := kernel_bounds_1900
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1900
  have h : (((225625 / 128 : ℚ) : ℝ) * (logKernel ((1899 / 64 : ℚ) : ℝ) - logKernel ((475 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((475 / 16 : ℚ) : ℝ) + Real.log ((475 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((4251749911985137 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_59 : ((244365478568505985 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1901 / 64 : ℚ) : ℝ) ∧
    Real.log ((1901 / 64 : ℚ) : ℝ) ≤ ((61091369642126497 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((244365478568505985 / 72057594037927936 : ℚ) : ℝ) ≤ ((1901 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1901 / 64 : ℚ) : ℝ) ≤ Real.exp ((61091369642126497 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_59 : heightPower (59 : Fin 988) ≤ ((67114348731501 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_59
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_59 : heightFactor (59 : Fin 988) ≤ ((2106429938213759 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_59
  obtain ⟨hpl, hph⟩ := kernel_bounds_1900
  obtain ⟨hcl, hch⟩ := kernel_bounds_1901
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1901
  have h : (((3613801 / 2048 : ℚ) : ℝ) * (logKernel ((475 / 16 : ℚ) : ℝ) - logKernel ((1901 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1901 / 64 : ℚ) : ℝ) + Real.log ((1901 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((2106429938213759 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_60 : ((122201686850831663 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((951 / 32 : ℚ) : ℝ) ∧
    Real.log ((951 / 32 : ℚ) : ℝ) ≤ ((244403373701663329 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((122201686850831663 / 36028797018963968 : ℚ) : ℝ) ≤ ((951 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((951 / 32 : ℚ) : ℝ) ≤ Real.exp ((244403373701663329 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_60 : heightPower (60 : Fin 988) ≤ ((68250867325251 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_60
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_60 : heightFactor (60 : Fin 988) ≤ ((2087161433091483 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_60
  obtain ⟨hpl, hph⟩ := kernel_bounds_1901
  obtain ⟨hcl, hch⟩ := kernel_bounds_1902
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1902
  have h : (((904401 / 512 : ℚ) : ℝ) * (logKernel ((1901 / 64 : ℚ) : ℝ) - logKernel ((951 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((951 / 32 : ℚ) : ℝ) + Real.log ((951 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((2087161433091483 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_61 : ((122220624458110753 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((1903 / 64 : ℚ) : ℝ) ∧
    Real.log ((1903 / 64 : ℚ) : ℝ) ≤ ((244441248916221509 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((122220624458110753 / 36028797018963968 : ℚ) : ℝ) ≤ ((1903 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1903 / 64 : ℚ) : ℝ) ≤ Real.exp ((244441248916221509 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_61 : heightPower (61 : Fin 988) ≤ ((17346841616811 / 17592186044416 : ℚ) : ℝ) := by
  have hh := log_height_bounds_61
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_61 : heightFactor (61 : Fin 988) ≤ ((2068067852153693 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_61
  obtain ⟨hpl, hph⟩ := kernel_bounds_1902
  obtain ⟨hcl, hch⟩ := kernel_bounds_1903
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1903
  have h : (((3621409 / 2048 : ℚ) : ℝ) * (logKernel ((951 / 32 : ℚ) : ℝ) - logKernel ((1903 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1903 / 64 : ℚ) : ℝ) + Real.log ((1903 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((2068067852153693 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_62 : ((122239552116554461 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((119 / 4 : ℚ) : ℝ) ∧
    Real.log ((119 / 4 : ℚ) : ℝ) ≤ ((244479104233108925 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((122239552116554461 / 36028797018963968 : ℚ) : ℝ) ≤ ((119 / 4 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((119 / 4 : ℚ) : ℝ) ≤ Real.exp ((244479104233108925 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_62 : heightPower (62 : Fin 988) ≤ ((282095384711671 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_62
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_62 : heightFactor (62 : Fin 988) ≤ ((4098295242162701 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_62
  obtain ⟨hpl, hph⟩ := kernel_bounds_1903
  obtain ⟨hcl, hch⟩ := kernel_bounds_1904
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1904
  have h : (((14161 / 8 : ℚ) : ℝ) * (logKernel ((1903 / 64 : ℚ) : ℝ) - logKernel ((119 / 4 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((119 / 4 : ℚ) : ℝ) + Real.log ((119 / 4 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((4098295242162701 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_63 : ((122258469836610501 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((1905 / 64 : ℚ) : ℝ) ∧
    Real.log ((1905 / 64 : ℚ) : ℝ) ≤ ((244516939673221005 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((122258469836610501 / 36028797018963968 : ℚ) : ℝ) ≤ ((1905 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1905 / 64 : ℚ) : ℝ) ≤ Real.exp ((244516939673221005 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_63 : heightPower (63 : Fin 988) ≤ ((286641225910713 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_63
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_63 : heightFactor (63 : Fin 988) ≤ ((4060798359167571 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_63
  obtain ⟨hpl, hph⟩ := kernel_bounds_1904
  obtain ⟨hcl, hch⟩ := kernel_bounds_1905
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1905
  have h : (((3629025 / 2048 : ℚ) : ℝ) * (logKernel ((119 / 4 : ℚ) : ℝ) - logKernel ((1905 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1905 / 64 : ℚ) : ℝ) + Real.log ((1905 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((4060798359167571 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

end LegendreK6.M2Pilot.Enclosures.Height001
