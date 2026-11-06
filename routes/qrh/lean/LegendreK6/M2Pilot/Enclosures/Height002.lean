import LegendreK6.M2PilotDefinitions
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp

/-! Generated proposals: every bound is checked by Lean, not by trusting Arb. -/
namespace LegendreK6.M2Pilot.Enclosures.Height002
set_option maxRecDepth 100000
set_option maxHeartbeats 0

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

theorem height_z_bounds_1906 : ((3238828680412863619 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((953 / 32 : ℚ) : ℝ) ∧
    heightZ ((953 / 32 : ℚ) : ℝ) ≤ ((1619414340206431811 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((3238828680412863619 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((953 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((5 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((953 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((5 / 96 : ℚ) : ℝ) ≤ ((1619414340206431811 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1906 : ((26119586132361801 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((953 / 32 : ℚ) : ℝ) ∧
    logKernel ((953 / 32 : ℚ) : ℝ) ≤ ((13059793066180903 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1906
  constructor
  · exact (show ((26119586132361801 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((3238828680412863619 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((953 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1619414340206431811 / 9223372036854775808 : ℚ) : ℝ) ≤ ((13059793066180903 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1907 : ((3188615295937392823 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1907 / 64 : ℚ) : ℝ) ∧
    heightZ ((1907 / 64 : ℚ) : ℝ) ≤ ((1594307647968696413 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((3188615295937392823 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1907 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((7 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((1907 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((7 / 192 : ℚ) : ℝ) ≤ ((1594307647968696413 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1907 : ((25714639483366069 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1907 / 64 : ℚ) : ℝ) ∧
    logKernel ((1907 / 64 : ℚ) : ℝ) ≤ ((12857319741683037 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1907
  constructor
  · exact (show ((25714639483366069 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((3188615295937392823 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1907 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1594307647968696413 / 9223372036854775808 : ℚ) : ℝ) ≤ ((12857319741683037 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1908 : ((3139180397831309135 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((477 / 16 : ℚ) : ℝ) ∧
    heightZ ((477 / 16 : ℚ) : ℝ) ≤ ((1569590198915654569 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((3139180397831309135 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((477 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((1 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((477 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((1 / 48 : ℚ) : ℝ) ≤ ((1569590198915654569 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1908 : ((25315970950252491 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((477 / 16 : ℚ) : ℝ) ∧
    logKernel ((477 / 16 : ℚ) : ℝ) ≤ ((1582248184390781 / 4503599627370496 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1908
  constructor
  · exact (show ((25315970950252491 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((3139180397831309135 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((477 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1569590198915654569 / 9223372036854775808 : ℚ) : ℝ) ≤ ((1582248184390781 / 4503599627370496 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1909 : ((772627979195536083 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((1909 / 64 : ℚ) : ℝ) ∧
    heightZ ((1909 / 64 : ℚ) : ℝ) ≤ ((3090511916782144335 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((772627979195536083 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((1909 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((1 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((1909 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((1 / 192 : ℚ) : ℝ) ≤ ((3090511916782144335 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1909 : ((194714712498875 / 562949953421312 : ℚ) : ℝ) ≤ logKernel ((1909 / 64 : ℚ) : ℝ) ∧
    logKernel ((1909 / 64 : ℚ) : ℝ) ≤ ((24923483199856005 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1909
  constructor
  · exact (show ((194714712498875 / 562949953421312 : ℚ) : ℝ) ≤ zKernel ((772627979195536083 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1909 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((3090511916782144335 / 18446744073709551616 : ℚ) : ℝ) ≤ ((24923483199856005 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1910 : ((380324746324347043 / 2305843009213693952 : ℚ) : ℝ) ≤ heightZ ((955 / 32 : ℚ) : ℝ) ∧
    heightZ ((955 / 32 : ℚ) : ℝ) ≤ ((3042597970594776347 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((380324746324347043 / 2305843009213693952 : ℚ) : ℝ) ≤ Real.exp (-((955 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((955 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1 / 96 : ℚ) : ℝ) ≤ ((3042597970594776347 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1910 : ((24537080408022387 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((955 / 32 : ℚ) : ℝ) ∧
    logKernel ((955 / 32 : ℚ) : ℝ) ≤ ((3067135051002799 / 9007199254740992 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1910
  constructor
  · exact (show ((24537080408022387 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((380324746324347043 / 2305843009213693952 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((955 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((3042597970594776347 / 18446744073709551616 : ℚ) : ℝ) ≤ ((3067135051002799 / 9007199254740992 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1911 : ((1497713430645221843 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((1911 / 64 : ℚ) : ℝ) ∧
    heightZ ((1911 / 64 : ℚ) : ℝ) ≤ ((2995426861290443689 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((1497713430645221843 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((1911 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-5 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((1911 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-5 / 192 : ℚ) : ℝ) ≤ ((2995426861290443689 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1911 : ((24156668236213253 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1911 / 64 : ℚ) : ℝ) ∧
    logKernel ((1911 / 64 : ℚ) : ℝ) ≤ ((12078334118106629 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1911
  constructor
  · exact (show ((24156668236213253 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((1497713430645221843 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1911 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((2995426861290443689 / 18446744073709551616 : ℚ) : ℝ) ≤ ((12078334118106629 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1912 : ((737246768062683879 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((239 / 8 : ℚ) : ℝ) ∧
    heightZ ((239 / 8 : ℚ) : ℝ) ≤ ((2948987072250735519 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((737246768062683879 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((239 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1 / 24 : ℚ) : ℝ) ∧
      Real.exp (-((239 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1 / 24 : ℚ) : ℝ) ≤ ((2948987072250735519 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1912 : ((23782153808473671 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((239 / 8 : ℚ) : ℝ) ∧
    logKernel ((239 / 8 : ℚ) : ℝ) ≤ ((5945538452118419 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1912
  constructor
  · exact (show ((23782153808473671 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((737246768062683879 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((239 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((2948987072250735519 / 18446744073709551616 : ℚ) : ℝ) ≤ ((5945538452118419 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1913 : ((2903267265405860005 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1913 / 64 : ℚ) : ℝ) ∧
    heightZ ((1913 / 64 : ℚ) : ℝ) ≤ ((362908408175732501 / 2305843009213693952 : ℚ) : ℝ) := by
  have h : ((2903267265405860005 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1913 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-11 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((1913 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-11 / 192 : ℚ) : ℝ) ≤ ((362908408175732501 / 2305843009213693952 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1913 : ((23413445688756933 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1913 / 64 : ℚ) : ℝ) ∧
    logKernel ((1913 / 64 : ℚ) : ℝ) ≤ ((11706722844378469 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1913
  constructor
  · exact (show ((23413445688756933 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((2903267265405860005 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1913 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((362908408175732501 / 2305843009213693952 : ℚ) : ℝ) ≤ ((11706722844378469 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1914 : ((1429128139233252291 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((957 / 32 : ℚ) : ℝ) ∧
    heightZ ((957 / 32 : ℚ) : ℝ) ≤ ((2858256278466504585 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((1429128139233252291 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((957 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-7 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((957 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-7 / 96 : ℚ) : ℝ) ≤ ((2858256278466504585 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1914 : ((23050453858600841 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((957 / 32 : ℚ) : ℝ) ∧
    logKernel ((957 / 32 : ℚ) : ℝ) ≤ ((11525226929300423 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1914
  constructor
  · exact (show ((23050453858600841 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((1429128139233252291 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((957 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((2858256278466504585 / 18446744073709551616 : ℚ) : ℝ) ≤ ((11525226929300423 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1915 : ((2813943122198612195 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1915 / 64 : ℚ) : ℝ) ∧
    heightZ ((1915 / 64 : ℚ) : ℝ) ≤ ((1406971561099306099 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((2813943122198612195 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1915 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-17 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((1915 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-17 / 192 : ℚ) : ℝ) ≤ ((1406971561099306099 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1915 : ((1418318105946881 / 4503599627370496 : ℚ) : ℝ) ≤ logKernel ((1915 / 64 : ℚ) : ℝ) ∧
    logKernel ((1915 / 64 : ℚ) : ℝ) ≤ ((22693089695150101 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1915
  constructor
  · exact (show ((1418318105946881 / 4503599627370496 : ℚ) : ℝ) ≤ zKernel ((2813943122198612195 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1915 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1406971561099306099 / 9223372036854775808 : ℚ) : ℝ) ≤ ((22693089695150101 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1916 : ((2770316977740408259 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((479 / 16 : ℚ) : ℝ) ∧
    heightZ ((479 / 16 : ℚ) : ℝ) ≤ ((1385158488870204131 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((2770316977740408259 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((479 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-5 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((479 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-5 / 48 : ℚ) : ℝ) ≤ ((1385158488870204131 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1916 : ((22341265949519419 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((479 / 16 : ℚ) : ℝ) ∧
    logKernel ((479 / 16 : ℚ) : ℝ) ≤ ((349082280461241 / 1125899906842624 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1916
  constructor
  · exact (show ((22341265949519419 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((2770316977740408259 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((479 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1385158488870204131 / 9223372036854775808 : ℚ) : ℝ) ≤ ((349082280461241 / 1125899906842624 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1917 : ((2727367193961023241 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1917 / 64 : ℚ) : ℝ) ∧
    heightZ ((1917 / 64 : ℚ) : ℝ) ≤ ((681841798490255811 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((2727367193961023241 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1917 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-23 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((1917 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-23 / 192 : ℚ) : ℝ) ≤ ((681841798490255811 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1917 : ((2749362090686515 / 9007199254740992 : ℚ) : ℝ) ≤ logKernel ((1917 / 64 : ℚ) : ℝ) ∧
    logKernel ((1917 / 64 : ℚ) : ℝ) ≤ ((21994896725492125 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1917
  constructor
  · exact (show ((2749362090686515 / 9007199254740992 : ℚ) : ℝ) ≤ zKernel ((2727367193961023241 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1917 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((681841798490255811 / 4611686018427387904 : ℚ) : ℝ) ≤ ((21994896725492125 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1918 : ((2685083284860066007 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((959 / 32 : ℚ) : ℝ) ∧
    heightZ ((959 / 32 : ℚ) : ℝ) ≤ ((1342541642430033005 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((2685083284860066007 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((959 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-13 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((959 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-13 / 96 : ℚ) : ℝ) ≤ ((1342541642430033005 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1918 : ((21653897458548917 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((959 / 32 : ℚ) : ℝ) ∧
    logKernel ((959 / 32 : ℚ) : ℝ) ≤ ((10826948729274461 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1918
  constructor
  · exact (show ((21653897458548917 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((2685083284860066007 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((959 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1342541642430033005 / 9223372036854775808 : ℚ) : ℝ) ≤ ((10826948729274461 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1919 : ((330431865875939131 / 2305843009213693952 : ℚ) : ℝ) ≤ heightZ ((1919 / 64 : ℚ) : ℝ) ∧
    heightZ ((1919 / 64 : ℚ) : ℝ) ≤ ((2643454927007513051 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((330431865875939131 / 2305843009213693952 : ℚ) : ℝ) ≤ Real.exp (-((1919 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-29 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((1919 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-29 / 192 : ℚ) : ℝ) ≤ ((2643454927007513051 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1919 : ((21318184895221877 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1919 / 64 : ℚ) : ℝ) ∧
    logKernel ((1919 / 64 : ℚ) : ℝ) ≤ ((10659092447610941 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1919
  constructor
  · exact (show ((21318184895221877 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((330431865875939131 / 2305843009213693952 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1919 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((2643454927007513051 / 18446744073709551616 : ℚ) : ℝ) ≤ ((10659092447610941 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1920 : ((2602471957023288545 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((30 / 1 : ℚ) : ℝ) ∧
    heightZ ((30 / 1 : ℚ) : ℝ) ≤ ((650617989255822137 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((2602471957023288545 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((30 / 1 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1 / 6 : ℚ) : ℝ) ∧
      Real.exp (-((30 / 1 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1 / 6 : ℚ) : ℝ) ≤ ((650617989255822137 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1920 : ((10493838536384227 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((30 / 1 : ℚ) : ℝ) ∧
    logKernel ((30 / 1 : ℚ) : ℝ) ≤ ((20987677072768459 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1920
  constructor
  · exact (show ((10493838536384227 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((2602471957023288545 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((30 / 1 : ℚ) : ℝ)) hh).trans
      (show zKernel ((650617989255822137 / 4611686018427387904 : ℚ) : ℝ) ≤ ((20987677072768459 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1921 : ((640531092273979981 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((1921 / 64 : ℚ) : ℝ) ∧
    heightZ ((1921 / 64 : ℚ) : ℝ) ≤ ((2562124369095919927 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((640531092273979981 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((1921 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-35 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((1921 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-35 / 192 : ℚ) : ℝ) ≤ ((2562124369095919927 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1921 : ((10331146649580321 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((1921 / 64 : ℚ) : ℝ) ∧
    logKernel ((1921 / 64 : ℚ) : ℝ) ≤ ((20662293299160647 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1921
  constructor
  · exact (show ((10331146649580321 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((640531092273979981 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1921 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((2562124369095919927 / 18446744073709551616 : ℚ) : ℝ) ≤ ((20662293299160647 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1922 : ((2522402312539663085 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((961 / 32 : ℚ) : ℝ) ∧
    heightZ ((961 / 32 : ℚ) : ℝ) ≤ ((157650144533728943 / 1152921504606846976 : ℚ) : ℝ) := by
  have h : ((2522402312539663085 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((961 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-19 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((961 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-19 / 96 : ℚ) : ℝ) ≤ ((157650144533728943 / 1152921504606846976 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1922 : ((20341954133384377 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((961 / 32 : ℚ) : ℝ) ∧
    logKernel ((961 / 32 : ℚ) : ℝ) ≤ ((10170977066692191 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1922
  constructor
  · exact (show ((20341954133384377 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((2522402312539663085 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((961 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((157650144533728943 / 1152921504606846976 : ℚ) : ℝ) ≤ ((10170977066692191 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1923 : ((310412011173687613 / 2305843009213693952 : ℚ) : ℝ) ≤ heightZ ((1923 / 64 : ℚ) : ℝ) ∧
    heightZ ((1923 / 64 : ℚ) : ℝ) ≤ ((2483296089389500907 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((310412011173687613 / 2305843009213693952 : ℚ) : ℝ) ≤ Real.exp (-((1923 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-41 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((1923 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-41 / 192 : ℚ) : ℝ) ≤ ((2483296089389500907 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1923 : ((2503322670755545 / 9007199254740992 : ℚ) : ℝ) ≤ logKernel ((1923 / 64 : ℚ) : ℝ) ∧
    logKernel ((1923 / 64 : ℚ) : ℝ) ≤ ((20026581366044365 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1923
  constructor
  · exact (show ((2503322670755545 / 9007199254740992 : ℚ) : ℝ) ≤ zKernel ((310412011173687613 / 2305843009213693952 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1923 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((2483296089389500907 / 18446744073709551616 : ℚ) : ℝ) ≤ ((20026581366044365 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1924 : ((2444796152033427819 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((481 / 16 : ℚ) : ℝ) ∧
    heightZ ((481 / 16 : ℚ) : ℝ) ≤ ((1222398076016713911 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((2444796152033427819 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((481 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-11 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((481 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-11 / 48 : ℚ) : ℝ) ≤ ((1222398076016713911 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1924 : ((19716098000269577 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((481 / 16 : ℚ) : ℝ) ∧
    logKernel ((481 / 16 : ℚ) : ℝ) ≤ ((9858049000134791 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1924
  constructor
  · exact (show ((19716098000269577 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((2444796152033427819 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((481 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1222398076016713911 / 9223372036854775808 : ℚ) : ℝ) ≤ ((9858049000134791 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1925 : ((1203446550440721221 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((1925 / 64 : ℚ) : ℝ) ∧
    heightZ ((1925 / 64 : ℚ) : ℝ) ≤ ((2406893100881442445 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((1203446550440721221 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((1925 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-47 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((1925 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-47 / 192 : ℚ) : ℝ) ≤ ((2406893100881442445 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1925 : ((2426303529114357 / 9007199254740992 : ℚ) : ℝ) ≤ logKernel ((1925 / 64 : ℚ) : ℝ) ∧
    logKernel ((1925 / 64 : ℚ) : ℝ) ≤ ((19410428232914861 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1925
  constructor
  · exact (show ((2426303529114357 / 9007199254740992 : ℚ) : ℝ) ≤ zKernel ((1203446550440721221 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1925 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((2406893100881442445 / 18446744073709551616 : ℚ) : ℝ) ≤ ((19410428232914861 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1926 : ((2369577682070679099 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((963 / 32 : ℚ) : ℝ) ∧
    heightZ ((963 / 32 : ℚ) : ℝ) ≤ ((1184788841035339551 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((2369577682070679099 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((963 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-25 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((963 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-25 / 96 : ℚ) : ℝ) ≤ ((1184788841035339551 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1926 : ((19109497436053861 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((963 / 32 : ℚ) : ℝ) ∧
    logKernel ((963 / 32 : ℚ) : ℝ) ≤ ((9554748718026933 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1926
  constructor
  · exact (show ((19109497436053861 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((2369577682070679099 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((963 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1184788841035339551 / 9223372036854775808 : ℚ) : ℝ) ≤ ((9554748718026933 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1927 : ((2332840785206117993 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1927 / 64 : ℚ) : ℝ) ∧
    heightZ ((1927 / 64 : ℚ) : ℝ) ≤ ((583210196301529499 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((2332840785206117993 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1927 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-53 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((1927 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-53 / 192 : ℚ) : ℝ) ≤ ((583210196301529499 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1927 : ((9406616069379507 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((1927 / 64 : ℚ) : ℝ) ∧
    logKernel ((1927 / 64 : ℚ) : ℝ) ≤ ((18813232138759019 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1927
  constructor
  · exact (show ((9406616069379507 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((2332840785206117993 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1927 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((583210196301529499 / 4611686018427387904 : ℚ) : ℝ) ≤ ((18813232138759019 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1928 : ((2296673441136322425 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((241 / 8 : ℚ) : ℝ) ∧
    heightZ ((241 / 8 : ℚ) : ℝ) ≤ ((574168360284080607 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((2296673441136322425 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((241 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-7 / 24 : ℚ) : ℝ) ∧
      Real.exp (-((241 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-7 / 24 : ℚ) : ℝ) ≤ ((574168360284080607 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1928 : ((1157597500572743 / 4503599627370496 : ℚ) : ℝ) ≤ logKernel ((241 / 8 : ℚ) : ℝ) ∧
    logKernel ((241 / 8 : ℚ) : ℝ) ≤ ((18521560009163893 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1928
  constructor
  · exact (show ((1157597500572743 / 4503599627370496 : ℚ) : ℝ) ≤ zKernel ((2296673441136322425 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((241 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((574168360284080607 / 4611686018427387904 : ℚ) : ℝ) ≤ ((18521560009163893 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1929 : ((2261066819763660001 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1929 / 64 : ℚ) : ℝ) ∧
    heightZ ((1929 / 64 : ℚ) : ℝ) ≤ ((565266704940915001 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((2261066819763660001 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1929 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-59 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((1929 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-59 / 192 : ℚ) : ℝ) ≤ ((565266704940915001 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1929 : ((18234409836803707 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1929 / 64 : ℚ) : ℝ) ∧
    logKernel ((1929 / 64 : ℚ) : ℝ) ≤ ((142456326850029 / 562949953421312 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1929
  constructor
  · exact (show ((18234409836803707 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((2261066819763660001 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1929 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((565266704940915001 / 4611686018427387904 : ℚ) : ℝ) ≤ ((142456326850029 / 562949953421312 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1930 : ((556503056972118305 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((965 / 32 : ℚ) : ℝ) ∧
    heightZ ((965 / 32 : ℚ) : ℝ) ≤ ((2226012227888473223 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((556503056972118305 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((965 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-31 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((965 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-31 / 96 : ℚ) : ℝ) ≤ ((2226012227888473223 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1930 : ((4487927878807405 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((965 / 32 : ℚ) : ℝ) ∧
    logKernel ((965 / 32 : ℚ) : ℝ) ≤ ((17951711515229625 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1930
  constructor
  · exact (show ((4487927878807405 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((556503056972118305 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((965 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((2226012227888473223 / 18446744073709551616 : ℚ) : ℝ) ≤ ((17951711515229625 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1931 : ((2191501107086673097 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1931 / 64 : ℚ) : ℝ) ∧
    heightZ ((1931 / 64 : ℚ) : ℝ) ≤ ((547875276771668275 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((2191501107086673097 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1931 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-65 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((1931 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-65 / 192 : ℚ) : ℝ) ≤ ((547875276771668275 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1931 : ((8836698012446261 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((1931 / 64 : ℚ) : ℝ) ∧
    logKernel ((1931 / 64 : ℚ) : ℝ) ≤ ((17673396024892527 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1931
  constructor
  · exact (show ((8836698012446261 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((2191501107086673097 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1931 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((547875276771668275 / 4611686018427387904 : ℚ) : ℝ) ≤ ((17673396024892527 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1932 : ((1078762515810118821 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((483 / 16 : ℚ) : ℝ) ∧
    heightZ ((483 / 16 : ℚ) : ℝ) ≤ ((2157525031620237645 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((1078762515810118821 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((483 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-17 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((483 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-17 / 48 : ℚ) : ℝ) ≤ ((2157525031620237645 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1932 : ((17399395416292237 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((483 / 16 : ℚ) : ℝ) ∧
    logKernel ((483 / 16 : ℚ) : ℝ) ≤ ((8699697708146121 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1932
  constructor
  · exact (show ((17399395416292237 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((1078762515810118821 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((483 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((2157525031620237645 / 18446744073709551616 : ℚ) : ℝ) ≤ ((8699697708146121 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1933 : ((1062037853190052533 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((1933 / 64 : ℚ) : ℝ) ∧
    heightZ ((1933 / 64 : ℚ) : ℝ) ≤ ((2124075706380105069 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((1062037853190052533 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((1933 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-71 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((1933 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-71 / 192 : ℚ) : ℝ) ≤ ((2124075706380105069 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1933 : ((8564821396693971 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((1933 / 64 : ℚ) : ℝ) ∧
    logKernel ((1933 / 64 : ℚ) : ℝ) ≤ ((17129642793387947 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1933
  constructor
  · exact (show ((8564821396693971 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((1062037853190052533 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1933 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((2124075706380105069 / 18446744073709551616 : ℚ) : ℝ) ≤ ((17129642793387947 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1934 : ((2091144964860959469 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((967 / 32 : ℚ) : ℝ) ∧
    heightZ ((967 / 32 : ℚ) : ℝ) ≤ ((130696560303809967 / 1152921504606846976 : ℚ) : ℝ) := by
  have h : ((2091144964860959469 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((967 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-37 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((967 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-37 / 96 : ℚ) : ℝ) ≤ ((130696560303809967 / 1152921504606846976 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1934 : ((2108009037158225 / 9007199254740992 : ℚ) : ℝ) ≤ logKernel ((967 / 32 : ℚ) : ℝ) ∧
    logKernel ((967 / 32 : ℚ) : ℝ) ≤ ((16864072297265805 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1934
  constructor
  · exact (show ((2108009037158225 / 9007199254740992 : ℚ) : ℝ) ≤ zKernel ((2091144964860959469 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((967 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((130696560303809967 / 1152921504606846976 : ℚ) : ℝ) ≤ ((16864072297265805 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1935 : ((2058724767167414559 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1935 / 64 : ℚ) : ℝ) ∧
    heightZ ((1935 / 64 : ℚ) : ℝ) ≤ ((1029362383583707281 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((2058724767167414559 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1935 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-77 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((1935 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-77 / 192 : ℚ) : ℝ) ≤ ((1029362383583707281 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1935 : ((1037663693128737 / 4503599627370496 : ℚ) : ℝ) ≤ logKernel ((1935 / 64 : ℚ) : ℝ) ∧
    logKernel ((1935 / 64 : ℚ) : ℝ) ≤ ((16602619090059797 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1935
  constructor
  · exact (show ((1037663693128737 / 4503599627370496 : ℚ) : ℝ) ≤ zKernel ((2058724767167414559 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1935 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1029362383583707281 / 9223372036854775808 : ℚ) : ℝ) ≤ ((16602619090059797 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1936 : ((2026807198051108635 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((121 / 4 : ℚ) : ℝ) ∧
    heightZ ((121 / 4 : ℚ) : ℝ) ≤ ((1013403599025554319 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((2026807198051108635 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((121 / 4 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-5 / 12 : ℚ) : ℝ) ∧
      Real.exp (-((121 / 4 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-5 / 12 : ℚ) : ℝ) ≤ ((1013403599025554319 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1936 : ((16345219339121841 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((121 / 4 : ℚ) : ℝ) ∧
    logKernel ((121 / 4 : ℚ) : ℝ) ≤ ((8172609669560923 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1936
  constructor
  · exact (show ((16345219339121841 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((2026807198051108635 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((121 / 4 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1013403599025554319 / 9223372036854775808 : ℚ) : ℝ) ≤ ((8172609669560923 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_1937 : ((1995384464978231591 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1937 / 64 : ℚ) : ℝ) ∧
    heightZ ((1937 / 64 : ℚ) : ℝ) ≤ ((997692232489115797 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((1995384464978231591 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1937 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-83 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((1937 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-83 / 192 : ℚ) : ℝ) ≤ ((997692232489115797 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_1937 : ((16091810201437349 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1937 / 64 : ℚ) : ℝ) ∧
    logKernel ((1937 / 64 : ℚ) : ℝ) ≤ ((8045905100718677 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_1937
  constructor
  · exact (show ((16091810201437349 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((1995384464978231591 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1937 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((997692232489115797 / 9223372036854775808 : ℚ) : ℝ) ≤ ((8045905100718677 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem log_height_bounds_64 : ((244554755257420277 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((953 / 32 : ℚ) : ℝ) ∧
    Real.log ((953 / 32 : ℚ) : ℝ) ≤ ((30569344407177535 / 9007199254740992 : ℚ) : ℝ) := by
  have hl : Real.exp ((244554755257420277 / 72057594037927936 : ℚ) : ℝ) ≤ ((953 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((953 / 32 : ℚ) : ℝ) ≤ Real.exp ((30569344407177535 / 9007199254740992 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_64 : heightPower (64 : Fin 988) ≤ ((291186989547595 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_64
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_64 : heightFactor (64 : Fin 988) ≤ ((3929337854053 / 274877906944 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_64
  obtain ⟨hpl, hph⟩ := kernel_bounds_1905
  obtain ⟨hcl, hch⟩ := kernel_bounds_1906
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1906
  have h : (((908209 / 512 : ℚ) : ℝ) * (logKernel ((1905 / 64 : ℚ) : ℝ) - logKernel ((953 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((953 / 32 : ℚ) : ℝ) + Real.log ((953 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((3929337854053 / 274877906944 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_65 : ((244592551006536451 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1907 / 64 : ℚ) : ℝ) ∧
    Real.log ((1907 / 64 : ℚ) : ℝ) ≤ ((122296275503268227 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((244592551006536451 / 72057594037927936 : ℚ) : ℝ) ≤ ((1907 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1907 / 64 : ℚ) : ℝ) ≤ Real.exp ((122296275503268227 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_65 : heightPower (65 : Fin 988) ≤ ((295732675703685 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_65
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_65 : heightFactor (65 : Fin 988) ≤ ((3986822987103729 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_65
  obtain ⟨hpl, hph⟩ := kernel_bounds_1906
  obtain ⟨hcl, hch⟩ := kernel_bounds_1907
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1907
  have h : (((3636649 / 2048 : ℚ) : ℝ) * (logKernel ((953 / 32 : ℚ) : ℝ) - logKernel ((1907 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1907 / 64 : ℚ) : ℝ) + Real.log ((1907 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((3986822987103729 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_66 : ((244630326941366465 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((477 / 16 : ℚ) : ℝ) ∧
    Real.log ((477 / 16 : ℚ) : ℝ) ≤ ((61157581735341617 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((244630326941366465 / 72057594037927936 : ℚ) : ℝ) ≤ ((477 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((477 / 16 : ℚ) : ℝ) ≤ Real.exp ((61157581735341617 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_66 : heightPower (66 : Fin 988) ≤ ((150139142230109 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_66
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_66 : heightFactor (66 : Fin 988) ≤ ((3950338394942673 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_66
  obtain ⟨hpl, hph⟩ := kernel_bounds_1907
  obtain ⟨hcl, hch⟩ := kernel_bounds_1908
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1908
  have h : (((227529 / 128 : ℚ) : ℝ) * (logKernel ((1907 / 64 : ℚ) : ℝ) - logKernel ((477 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((477 / 16 : ℚ) : ℝ) + Real.log ((477 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((3950338394942673 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_67 : ((244668083082674573 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1909 / 64 : ℚ) : ℝ) ∧
    Real.log ((1909 / 64 : ℚ) : ℝ) ≤ ((15291755192667161 / 4503599627370496 : ℚ) : ℝ) := by
  have hl : Real.exp ((244668083082674573 / 72057594037927936 : ℚ) : ℝ) ≤ ((1909 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1909 / 64 : ℚ) : ℝ) ≤ Real.exp ((15291755192667161 / 4503599627370496 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_67 : heightPower (67 : Fin 988) ≤ ((304823815898307 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_67
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_67 : heightFactor (67 : Fin 988) ≤ ((3914185175262905 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_67
  obtain ⟨hpl, hph⟩ := kernel_bounds_1908
  obtain ⟨hcl, hch⟩ := kernel_bounds_1909
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1909
  have h : (((3644281 / 2048 : ℚ) : ℝ) * (logKernel ((477 / 16 : ℚ) : ℝ) - logKernel ((1909 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1909 / 64 : ℚ) : ℝ) + Real.log ((1909 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((3914185175262905 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_68 : ((61176454862798101 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((955 / 32 : ℚ) : ℝ) ∧
    Real.log ((955 / 32 : ℚ) : ℝ) ≤ ((244705819451192407 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((61176454862798101 / 18014398509481984 : ℚ) : ℝ) ≤ ((955 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((955 / 32 : ℚ) : ℝ) ≤ Real.exp ((244705819451192407 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_68 : heightPower (68 : Fin 988) ≤ ((154684635049467 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_68
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_68 : heightFactor (68 : Fin 988) ≤ ((969590086025665 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_68
  obtain ⟨hpl, hph⟩ := kernel_bounds_1909
  obtain ⟨hcl, hch⟩ := kernel_bounds_1910
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1910
  have h : (((912025 / 512 : ℚ) : ℝ) * (logKernel ((1909 / 64 : ℚ) : ℝ) - logKernel ((955 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((955 / 32 : ℚ) : ℝ) + Real.log ((955 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((969590086025665 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_69 : ((30592942008452379 / 9007199254740992 : ℚ) : ℝ) ≤ Real.log ((1911 / 64 : ℚ) : ℝ) ∧
    Real.log ((1911 / 64 : ℚ) : ℝ) ≤ ((244743536067619035 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((30592942008452379 / 9007199254740992 : ℚ) : ℝ) ≤ ((1911 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1911 / 64 : ℚ) : ℝ) ≤ Real.exp ((244743536067619035 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_69 : heightPower (69 : Fin 988) ≤ ((156957323571477 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_69
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_69 : heightFactor (69 : Fin 988) ≤ ((3842860944106039 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_69
  obtain ⟨hpl, hph⟩ := kernel_bounds_1910
  obtain ⟨hcl, hch⟩ := kernel_bounds_1911
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1911
  have h : (((3651921 / 2048 : ℚ) : ℝ) * (logKernel ((955 / 32 : ℚ) : ℝ) - logKernel ((1911 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1911 / 64 : ℚ) : ℝ) + Real.log ((1911 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((3842860944106039 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_70 : ((30597654119077631 / 9007199254740992 : ℚ) : ℝ) ≤ Real.log ((239 / 8 : ℚ) : ℝ) ∧
    Real.log ((239 / 8 : ℚ) : ℝ) ≤ ((244781232952621051 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((30597654119077631 / 9007199254740992 : ℚ) : ℝ) ≤ ((239 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((239 / 8 : ℚ) : ℝ) ≤ Real.exp ((244781232952621051 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_70 : heightPower (70 : Fin 988) ≤ ((318459947111097 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_70
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_70 : heightFactor (70 : Fin 988) ≤ ((3807684044288503 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_70
  obtain ⟨hpl, hph⟩ := kernel_bounds_1911
  obtain ⟨hcl, hch⟩ := kernel_bounds_1912
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1912
  have h : (((57121 / 32 : ℚ) : ℝ) * (logKernel ((1911 / 64 : ℚ) : ℝ) - logKernel ((239 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((239 / 8 : ℚ) : ℝ) + Real.log ((239 / 8 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((3807684044288503 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_71 : ((122409455063416311 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((1913 / 64 : ℚ) : ℝ) ∧
    Real.log ((1913 / 64 : ℚ) : ℝ) ≤ ((244818910126832625 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((122409455063416311 / 36028797018963968 : ℚ) : ℝ) ≤ ((1913 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1913 / 64 : ℚ) : ℝ) ≤ Real.exp ((244818910126832625 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_71 : heightPower (71 : Fin 988) ≤ ((323005170083965 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_71
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_71 : heightFactor (71 : Fin 988) ≤ ((235801671237775 / 17592186044416 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_71
  obtain ⟨hpl, hph⟩ := kernel_bounds_1912
  obtain ⟨hcl, hch⟩ := kernel_bounds_1913
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1913
  have h : (((3659569 / 2048 : ℚ) : ℝ) * (logKernel ((239 / 8 : ℚ) : ℝ) - logKernel ((1913 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1913 / 64 : ℚ) : ℝ) + Real.log ((1913 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((235801671237775 / 17592186044416 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_72 : ((122428283805427787 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((957 / 32 : ℚ) : ℝ) ∧
    Real.log ((957 / 32 : ℚ) : ℝ) ≤ ((244856567610855577 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((122428283805427787 / 36028797018963968 : ℚ) : ℝ) ≤ ((957 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((957 / 32 : ℚ) : ℝ) ≤ Real.exp ((244856567610855577 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_72 : heightPower (72 : Fin 988) ≤ ((163775158071017 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_72
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_72 : heightFactor (72 : Fin 988) ≤ ((934571537929129 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_72
  obtain ⟨hpl, hph⟩ := kernel_bounds_1913
  obtain ⟨hcl, hch⟩ := kernel_bounds_1914
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1914
  have h : (((915849 / 512 : ℚ) : ℝ) * (logKernel ((1913 / 64 : ℚ) : ℝ) - logKernel ((957 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((957 / 32 : ℚ) : ℝ) + Real.log ((957 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((934571537929129 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_73 : ((244894205425259443 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1915 / 64 : ℚ) : ℝ) ∧
    Real.log ((1915 / 64 : ℚ) : ℝ) ≤ ((122447102712629723 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((244894205425259443 / 72057594037927936 : ℚ) : ℝ) ≤ ((1915 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1915 / 64 : ℚ) : ℝ) ≤ Real.exp ((122447102712629723 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_73 : heightPower (73 : Fin 988) ≤ ((332095385365653 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_73
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_73 : heightFactor (73 : Fin 988) ≤ ((3704059426767635 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_73
  obtain ⟨hpl, hph⟩ := kernel_bounds_1914
  obtain ⟨hcl, hch⟩ := kernel_bounds_1915
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1915
  have h : (((3667225 / 2048 : ℚ) : ℝ) * (logKernel ((957 / 32 : ℚ) : ℝ) - logKernel ((1915 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1915 / 64 : ℚ) : ℝ) + Real.log ((1915 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((3704059426767635 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_74 : ((122465911795290775 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((479 / 16 : ℚ) : ℝ) ∧
    Real.log ((479 / 16 : ℚ) : ℝ) ≤ ((244931823590581553 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((122465911795290775 / 36028797018963968 : ℚ) : ℝ) ≤ ((479 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((479 / 16 : ℚ) : ℝ) ≤ Real.exp ((244931823590581553 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_74 : heightPower (74 : Fin 988) ≤ ((336640377835047 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_74
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_74 : heightFactor (74 : Fin 988) ≤ ((3670143737154079 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_74
  obtain ⟨hpl, hph⟩ := kernel_bounds_1915
  obtain ⟨hcl, hch⟩ := kernel_bounds_1916
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1916
  have h : (((229441 / 128 : ℚ) : ℝ) * (logKernel ((1915 / 64 : ℚ) : ℝ) - logKernel ((479 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((479 / 16 : ℚ) : ℝ) + Real.log ((479 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((3670143737154079 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_75 : ((122484711063663535 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((1917 / 64 : ℚ) : ℝ) ∧
    Real.log ((1917 / 64 : ℚ) : ℝ) ≤ ((244969422127327073 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((122484711063663535 / 36028797018963968 : ℚ) : ℝ) ≤ ((1917 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1917 / 64 : ℚ) : ℝ) ≤ Real.exp ((244969422127327073 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_75 : heightPower (75 : Fin 988) ≤ ((341185293630313 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_75
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_75 : heightFactor (75 : Fin 988) ≤ ((3636536280301221 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_75
  obtain ⟨hpl, hph⟩ := kernel_bounds_1916
  obtain ⟨hcl, hch⟩ := kernel_bounds_1917
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1917
  have h : (((3674889 / 2048 : ℚ) : ℝ) * (logKernel ((479 / 16 : ℚ) : ℝ) - logKernel ((1917 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1917 / 64 : ℚ) : ℝ) + Real.log ((1917 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((3636536280301221 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_76 : ((30625875131996137 / 9007199254740992 : ℚ) : ℝ) ≤ Real.log ((959 / 32 : ℚ) : ℝ) ∧
    Real.log ((959 / 32 : ℚ) : ℝ) ≤ ((245007001055969099 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((30625875131996137 / 9007199254740992 : ℚ) : ℝ) ≤ ((959 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((959 / 32 : ℚ) : ℝ) ≤ Real.exp ((245007001055969099 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_76 : heightPower (76 : Fin 988) ≤ ((345730132831425 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_76
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_76 : heightFactor (76 : Fin 988) ≤ ((3603234278640953 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_76
  obtain ⟨hpl, hph⟩ := kernel_bounds_1917
  obtain ⟨hcl, hch⟩ := kernel_bounds_1918
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1918
  have h : (((919681 / 512 : ℚ) : ℝ) * (logKernel ((1917 / 64 : ℚ) : ℝ) - logKernel ((959 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((959 / 32 : ℚ) : ℝ) + Real.log ((959 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((3603234278640953 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_77 : ((122522280198474353 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((1919 / 64 : ℚ) : ℝ) ∧
    Real.log ((1919 / 64 : ℚ) : ℝ) ≤ ((245044560396948709 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((122522280198474353 / 36028797018963968 : ℚ) : ℝ) ≤ ((1919 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1919 / 64 : ℚ) : ℝ) ≤ Real.exp ((245044560396948709 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_77 : heightPower (77 : Fin 988) ≤ ((175137447759115 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_77
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_77 : heightFactor (77 : Fin 988) ≤ ((3570234979391089 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_77
  obtain ⟨hpl, hph⟩ := kernel_bounds_1918
  obtain ⟨hcl, hch⟩ := kernel_bounds_1919
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1919
  have h : (((3682561 / 2048 : ℚ) : ℝ) * (logKernel ((959 / 32 : ℚ) : ℝ) - logKernel ((1919 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1919 / 64 : ℚ) : ℝ) + Real.log ((1919 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((3570234979391089 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_78 : ((30635262521334379 / 9007199254740992 : ℚ) : ℝ) ≤ Real.log ((30 / 1 : ℚ) : ℝ) ∧
    Real.log ((30 / 1 : ℚ) : ℝ) ≤ ((245082100170675035 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((30635262521334379 / 9007199254740992 : ℚ) : ℝ) ≤ ((30 / 1 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((30 / 1 : ℚ) : ℝ) ≤ Real.exp ((245082100170675035 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_78 : heightPower (78 : Fin 988) ≤ ((354819581770453 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_78
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_78 : heightFactor (78 : Fin 988) ≤ ((1768767827168343 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_78
  obtain ⟨hpl, hph⟩ := kernel_bounds_1919
  obtain ⟨hcl, hch⟩ := kernel_bounds_1920
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1920
  have h : (((1800 / 1 : ℚ) : ℝ) * (logKernel ((1919 / 64 : ℚ) : ℝ) - logKernel ((30 / 1 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((30 / 1 : ℚ) : ℝ) + Real.log ((30 / 1 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1768767827168343 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_79 : ((61279905099381331 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((1921 / 64 : ℚ) : ℝ) ∧
    Real.log ((1921 / 64 : ℚ) : ℝ) ≤ ((245119620397525327 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((61279905099381331 / 18014398509481984 : ℚ) : ℝ) ≤ ((1921 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1921 / 64 : ℚ) : ℝ) ≤ Real.exp ((245119620397525327 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_79 : heightPower (79 : Fin 988) ≤ ((359364191667691 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_79
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_79 : heightFactor (79 : Fin 988) ≤ ((3505133599613275 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_79
  obtain ⟨hpl, hph⟩ := kernel_bounds_1920
  obtain ⟨hcl, hch⟩ := kernel_bounds_1921
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1921
  have h : (((3690241 / 2048 : ℚ) : ℝ) * (logKernel ((30 / 1 : ℚ) : ℝ) - logKernel ((1921 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1921 / 64 : ℚ) : ℝ) + Real.log ((1921 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((3505133599613275 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_80 : ((122578560548922509 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((961 / 32 : ℚ) : ℝ) ∧
    Real.log ((961 / 32 : ℚ) : ℝ) ≤ ((245157121097845021 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((122578560548922509 / 36028797018963968 : ℚ) : ℝ) ≤ ((961 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((961 / 32 : ℚ) : ℝ) ≤ Real.exp ((245157121097845021 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_80 : heightPower (80 : Fin 988) ≤ ((363908725289419 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_80
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_80 : heightFactor (80 : Fin 988) ≤ ((27133016683531 / 2199023255552 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_80
  obtain ⟨hpl, hph⟩ := kernel_bounds_1921
  obtain ⟨hcl, hch⟩ := kernel_bounds_1922
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1922
  have h : (((923521 / 512 : ℚ) : ℝ) * (logKernel ((1921 / 64 : ℚ) : ℝ) - logKernel ((961 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((961 / 32 : ℚ) : ℝ) + Real.log ((961 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((27133016683531 / 2199023255552 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_81 : ((245194602291947801 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1923 / 64 : ℚ) : ℝ) ∧
    Real.log ((1923 / 64 : ℚ) : ℝ) ≤ ((61298650572986951 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((245194602291947801 / 72057594037927936 : ℚ) : ℝ) ≤ ((1923 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1923 / 64 : ℚ) : ℝ) ≤ Real.exp ((61298650572986951 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_81 : heightPower (81 : Fin 988) ≤ ((368453182714987 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_81
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_81 : heightFactor (81 : Fin 988) ≤ ((1720605303083225 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_81
  obtain ⟨hpl, hph⟩ := kernel_bounds_1922
  obtain ⟨hcl, hch⟩ := kernel_bounds_1923
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1923
  have h : (((3697929 / 2048 : ℚ) : ℝ) * (logKernel ((961 / 32 : ℚ) : ℝ) - logKernel ((1923 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1923 / 64 : ℚ) : ℝ) + Real.log ((1923 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1720605303083225 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_82 : ((245232064000115679 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((481 / 16 : ℚ) : ℝ) ∧
    Real.log ((481 / 16 : ℚ) : ℝ) ≤ ((122616032000057841 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((245232064000115679 / 72057594037927936 : ℚ) : ℝ) ≤ ((481 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((481 / 16 : ℚ) : ℝ) ≤ Real.exp ((122616032000057841 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_82 : heightPower (82 : Fin 988) ≤ ((372997564023621 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_82
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_82 : heightFactor (82 : Fin 988) ≤ ((3409684379541815 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_82
  obtain ⟨hpl, hph⟩ := kernel_bounds_1923
  obtain ⟨hcl, hch⟩ := kernel_bounds_1924
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1924
  have h : (((231361 / 128 : ℚ) : ℝ) * (logKernel ((1923 / 64 : ℚ) : ℝ) - logKernel ((481 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((481 / 16 : ℚ) : ℝ) + Real.log ((481 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((3409684379541815 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_83 : ((122634753121299519 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((1925 / 64 : ℚ) : ℝ) ∧
    Real.log ((1925 / 64 : ℚ) : ℝ) ≤ ((245269506242599041 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((122634753121299519 / 36028797018963968 : ℚ) : ℝ) ≤ ((1925 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1925 / 64 : ℚ) : ℝ) ≤ Real.exp ((245269506242599041 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_83 : heightPower (83 : Fin 988) ≤ ((188770934647213 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_83
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_83 : heightFactor (83 : Fin 988) ≤ ((844611211756311 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_83
  obtain ⟨hpl, hph⟩ := kernel_bounds_1924
  obtain ⟨hcl, hch⟩ := kernel_bounds_1925
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1925
  have h : (((3705625 / 2048 : ℚ) : ℝ) * (logKernel ((481 / 16 : ℚ) : ℝ) - logKernel ((1925 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1925 / 64 : ℚ) : ℝ) + Real.log ((1925 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((844611211756311 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_84 : ((122653464519808359 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((963 / 32 : ℚ) : ℝ) ∧
    Real.log ((963 / 32 : ℚ) : ℝ) ≤ ((245306929039616721 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((122653464519808359 / 36028797018963968 : ℚ) : ℝ) ≤ ((963 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((963 / 32 : ℚ) : ℝ) ≤ Real.exp ((245306929039616721 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_84 : heightPower (84 : Fin 988) ≤ ((95521524651595 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_84
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_84 : heightFactor (84 : Fin 988) ≤ ((3347489423318511 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_84
  obtain ⟨hpl, hph⟩ := kernel_bounds_1925
  obtain ⟨hcl, hch⟩ := kernel_bounds_1926
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1926
  have h : (((927369 / 512 : ℚ) : ℝ) * (logKernel ((1925 / 64 : ℚ) : ℝ) - logKernel ((963 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((963 / 32 : ℚ) : ℝ) + Real.log ((963 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((3347489423318511 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_85 : ((245344332411356069 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1927 / 64 : ℚ) : ℝ) ∧
    Real.log ((1927 / 64 : ℚ) : ℝ) ≤ ((30668041551419509 / 9007199254740992 : ℚ) : ℝ) := by
  have hl : Real.exp ((245344332411356069 / 72057594037927936 : ℚ) : ℝ) ≤ ((1927 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1927 / 64 : ℚ) : ℝ) ≤ Real.exp ((30668041551419509 / 9007199254740992 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_85 : heightPower (85 : Fin 988) ≤ ((386630252038341 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_85
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_85 : heightFactor (85 : Fin 988) ≤ ((3316815546212291 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_85
  obtain ⟨hpl, hph⟩ := kernel_bounds_1926
  obtain ⟨hcl, hch⟩ := kernel_bounds_1927
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1927
  have h : (((3713329 / 2048 : ℚ) : ℝ) * (logKernel ((963 / 32 : ℚ) : ℝ) - logKernel ((1927 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1927 / 64 : ℚ) : ℝ) + Real.log ((1927 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((3316815546212291 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_86 : ((245381716377973025 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((241 / 8 : ℚ) : ℝ) ∧
    Real.log ((241 / 8 : ℚ) : ℝ) ≤ ((61345429094493257 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((245381716377973025 / 72057594037927936 : ℚ) : ℝ) ≤ ((241 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((241 / 8 : ℚ) : ℝ) ≤ Real.exp ((61345429094493257 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_86 : heightPower (86 : Fin 988) ≤ ((391174329669043 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_86
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_86 : heightFactor (86 : Fin 988) ≤ ((3286420676382263 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_86
  obtain ⟨hpl, hph⟩ := kernel_bounds_1927
  obtain ⟨hcl, hch⟩ := kernel_bounds_1928
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1928
  have h : (((58081 / 32 : ℚ) : ℝ) * (logKernel ((1927 / 64 : ℚ) : ℝ) - logKernel ((241 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((241 / 8 : ℚ) : ℝ) + Real.log ((241 / 8 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((3286420676382263 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_87 : ((245419080959592163 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1929 / 64 : ℚ) : ℝ) ∧
    Real.log ((1929 / 64 : ℚ) : ℝ) ≤ ((122709540479796083 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((245419080959592163 / 72057594037927936 : ℚ) : ℝ) ≤ ((1929 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1929 / 64 : ℚ) : ℝ) ≤ Real.exp ((122709540479796083 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_87 : heightPower (87 : Fin 988) ≤ ((49464791447137 / 35184372088832 : ℚ) : ℝ) := by
  have hh := log_height_bounds_87
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_87 : heightFactor (87 : Fin 988) ≤ ((3256302297186989 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_87
  obtain ⟨hpl, hph⟩ := kernel_bounds_1928
  obtain ⟨hcl, hch⟩ := kernel_bounds_1929
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1929
  have h : (((3721041 / 2048 : ℚ) : ℝ) * (logKernel ((241 / 8 : ℚ) : ℝ) - logKernel ((1929 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1929 / 64 : ℚ) : ℝ) + Real.log ((1929 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((3256302297186989 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_88 : ((245456426176306769 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((965 / 32 : ℚ) : ℝ) ∧
    Real.log ((965 / 32 : ℚ) : ℝ) ≤ ((61364106544076693 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((245456426176306769 / 72057594037927936 : ℚ) : ℝ) ≤ ((965 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((965 / 32 : ℚ) : ℝ) ≤ Real.exp ((61364106544076693 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_88 : heightPower (88 : Fin 988) ≤ ((12508195557531 / 8796093022208 : ℚ) : ℝ) := by
  have hh := log_height_bounds_88
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_88 : heightFactor (88 : Fin 988) ≤ ((3226457914467553 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_88
  obtain ⟨hpl, hph⟩ := kernel_bounds_1929
  obtain ⟨hcl, hch⟩ := kernel_bounds_1930
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1930
  have h : (((931225 / 512 : ℚ) : ℝ) * (logKernel ((1929 / 64 : ℚ) : ℝ) - logKernel ((965 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((965 / 32 : ℚ) : ℝ) + Real.log ((965 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((3226457914467553 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_89 : ((61373438012044727 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((1931 / 64 : ℚ) : ℝ) ∧
    Real.log ((1931 / 64 : ℚ) : ℝ) ≤ ((245493752048178911 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((61373438012044727 / 18014398509481984 : ℚ) : ℝ) ≤ ((1931 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1931 / 64 : ℚ) : ℝ) ≤ Real.exp ((245493752048178911 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_89 : heightPower (89 : Fin 988) ≤ ((50600763567387 / 35184372088832 : ℚ) : ℝ) := by
  have hh := log_height_bounds_89
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_89 : heightFactor (89 : Fin 988) ≤ ((1598442528174477 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_89
  obtain ⟨hpl, hph⟩ := kernel_bounds_1930
  obtain ⟨hcl, hch⟩ := kernel_bounds_1931
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1931
  have h : (((3728761 / 2048 : ℚ) : ℝ) * (logKernel ((965 / 32 : ℚ) : ℝ) - logKernel ((1931 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1931 / 64 : ℚ) : ℝ) + Real.log ((1931 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1598442528174477 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_90 : ((30691382324404935 / 9007199254740992 : ℚ) : ℝ) ≤ Real.log ((483 / 16 : ℚ) : ℝ) ∧
    Real.log ((483 / 16 : ℚ) : ℝ) ≤ ((245531058595239483 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((30691382324404935 / 9007199254740992 : ℚ) : ℝ) ≤ ((483 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((483 / 16 : ℚ) : ℝ) ≤ Real.exp ((245531058595239483 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_90 : heightPower (90 : Fin 988) ≤ ((51168735468707 / 35184372088832 : ℚ) : ℝ) := by
  have hh := log_height_bounds_90
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_90 : heightFactor (90 : Fin 988) ≤ ((1583790636521609 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_90
  obtain ⟨hpl, hph⟩ := kernel_bounds_1931
  obtain ⟨hcl, hch⟩ := kernel_bounds_1932
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1932
  have h : (((233289 / 128 : ℚ) : ℝ) * (logKernel ((1931 / 64 : ℚ) : ℝ) - logKernel ((483 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((483 / 16 : ℚ) : ℝ) + Real.log ((483 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1583790636521609 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_91 : ((61392086459372073 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((1933 / 64 : ℚ) : ℝ) ∧
    Real.log ((1933 / 64 : ℚ) : ℝ) ≤ ((245568345837488295 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((61392086459372073 / 18014398509481984 : ℚ) : ℝ) ≤ ((1933 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1933 / 64 : ℚ) : ℝ) ≤ Real.exp ((245568345837488295 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_91 : heightPower (91 : Fin 988) ≤ ((206946791775397 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_91
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_91 : heightFactor (91 : Fin 988) ≤ ((98079504270445 / 8796093022208 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_91
  obtain ⟨hpl, hph⟩ := kernel_bounds_1932
  obtain ⟨hcl, hch⟩ := kernel_bounds_1933
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1933
  have h : (((3736489 / 2048 : ℚ) : ℝ) * (logKernel ((483 / 16 : ℚ) : ℝ) - logKernel ((1933 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1933 / 64 : ℚ) : ℝ) + Real.log ((1933 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((98079504270445 / 8796093022208 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_92 : ((245605613794894119 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((967 / 32 : ℚ) : ℝ) ∧
    Real.log ((967 / 32 : ℚ) : ℝ) ≤ ((122802806897447061 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((245605613794894119 / 72057594037927936 : ℚ) : ℝ) ≤ ((967 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((967 / 32 : ℚ) : ℝ) ≤ Real.exp ((122802806897447061 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_92 : heightPower (92 : Fin 988) ≤ ((418437208020515 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_92
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_92 : heightFactor (92 : Fin 988) ≤ ((3109771240984317 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_92
  obtain ⟨hpl, hph⟩ := kernel_bounds_1933
  obtain ⟨hcl, hch⟩ := kernel_bounds_1934
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1934
  have h : (((935089 / 512 : ℚ) : ℝ) * (logKernel ((1933 / 64 : ℚ) : ℝ) - logKernel ((967 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((967 / 32 : ℚ) : ℝ) + Real.log ((967 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((3109771240984317 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_93 : ((245642862487394769 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1935 / 64 : ℚ) : ℝ) ∧
    Real.log ((1935 / 64 : ℚ) : ℝ) ≤ ((61410715621848693 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((245642862487394769 / 72057594037927936 : ℚ) : ℝ) ≤ ((1935 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1935 / 64 : ℚ) : ℝ) ≤ Real.exp ((61410715621848693 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_93 : heightPower (93 : Fin 988) ≤ ((422980757236699 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_93
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_93 : heightFactor (93 : Fin 988) ≤ ((3081260201342375 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_93
  obtain ⟨hpl, hph⟩ := kernel_bounds_1934
  obtain ⟨hcl, hch⟩ := kernel_bounds_1935
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1935
  have h : (((3744225 / 2048 : ℚ) : ℝ) * (logKernel ((967 / 32 : ℚ) : ℝ) - logKernel ((1935 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1935 / 64 : ℚ) : ℝ) + Real.log ((1935 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((3081260201342375 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_94 : ((245680091934897145 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((121 / 4 : ℚ) : ℝ) ∧
    Real.log ((121 / 4 : ℚ) : ℝ) ≤ ((61420022983724287 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((245680091934897145 / 72057594037927936 : ℚ) : ℝ) ≤ ((121 / 4 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((121 / 4 : ℚ) : ℝ) ≤ Real.exp ((61420022983724287 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_94 : heightPower (94 : Fin 988) ≤ ((427524231277109 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_94
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_94 : heightFactor (94 : Fin 988) ≤ ((3053008654353867 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_94
  obtain ⟨hpl, hph⟩ := kernel_bounds_1935
  obtain ⟨hcl, hch⟩ := kernel_bounds_1936
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1936
  have h : (((14641 / 8 : ℚ) : ℝ) * (logKernel ((1935 / 64 : ℚ) : ℝ) - logKernel ((121 / 4 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((121 / 4 : ℚ) : ℝ) + Real.log ((121 / 4 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((3053008654353867 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_95 : ((1919666423103729 / 562949953421312 : ℚ) : ℝ) ≤ Real.log ((1937 / 64 : ℚ) : ℝ) ∧
    Real.log ((1937 / 64 : ℚ) : ℝ) ≤ ((245717302157277315 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((1919666423103729 / 562949953421312 : ℚ) : ℝ) ≤ ((1937 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1937 / 64 : ℚ) : ℝ) ≤ Real.exp ((245717302157277315 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_95 : heightPower (95 : Fin 988) ≤ ((216033815109693 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_95
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_95 : heightFactor (95 : Fin 988) ≤ ((378126782221541 / 35184372088832 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_95
  obtain ⟨hpl, hph⟩ := kernel_bounds_1936
  obtain ⟨hcl, hch⟩ := kernel_bounds_1937
  obtain ⟨hzl, hzh⟩ := height_z_bounds_1937
  have h : (((3751969 / 2048 : ℚ) : ℝ) * (logKernel ((121 / 4 : ℚ) : ℝ) - logKernel ((1937 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1937 / 64 : ℚ) : ℝ) + Real.log ((1937 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((378126782221541 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

end LegendreK6.M2Pilot.Enclosures.Height002
