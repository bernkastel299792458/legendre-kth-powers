import LegendreK6.M2PilotDefinitions
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp

/-! Generated proposals: every bound is checked by Lean, not by trusting Arb. -/
namespace LegendreK6.M2Pilot
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem sigma_factor_upper_0 : sigmaFactor (0 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((5069 / 1000 : ℚ) : ℝ) * (Real.exp ((-937013 / 16384 : ℚ) : ℝ) - Real.exp ((-3663 / 64 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_0 : sigmaPower (0 : Fin 1536) ≤ ((187649984473771 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1535 : sigmaFactor (1535 : Fin 1536) ≤ ((296342023 / 35184372088832 : ℚ) : ℝ) := by
  have h : ((2177 / 100 : ℚ) : ℝ) * (Real.exp ((-311377 / 26816 : ℚ) : ℝ) - Real.exp ((-80012097 / 6864896 : ℚ) : ℝ)) ≤ ((296342023 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1535 : sigmaPower (1535 : Fin 1536) ≤ ((162855269667 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

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

theorem height_z_bounds_2828 : ((224255503247 / 2305843009213693952 : ℚ) : ℝ) ≤ heightZ ((707 / 16 : ℚ) : ℝ) ∧
    heightZ ((707 / 16 : ℚ) : ℝ) ≤ ((1794044025979 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((224255503247 / 2305843009213693952 : ℚ) : ℝ) ≤ Real.exp (-((707 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-689 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((707 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-689 / 48 : ℚ) : ℝ) ≤ ((1794044025979 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2828 : ((22513 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((707 / 16 : ℚ) : ℝ) ∧
    logKernel ((707 / 16 : ℚ) : ℝ) ≤ ((90057 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2828
  constructor
  · exact (show ((22513 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((224255503247 / 2305843009213693952 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((707 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1794044025979 / 18446744073709551616 : ℚ) : ℝ) ≤ ((90057 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2829 : ((441557487851 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((2829 / 64 : ℚ) : ℝ) ∧
    heightZ ((2829 / 64 : ℚ) : ℝ) ≤ ((1766229951407 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((441557487851 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((2829 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2759 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2829 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-2759 / 192 : ℚ) : ℝ) ≤ ((1766229951407 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2829 : ((87281 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2829 / 64 : ℚ) : ℝ) ∧
    logKernel ((2829 / 64 : ℚ) : ℝ) ≤ ((43643 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2829
  constructor
  · exact (show ((87281 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((441557487851 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2829 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((1766229951407 / 18446744073709551616 : ℚ) : ℝ) ≤ ((43643 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

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

theorem log_height_bounds_987 : ((273011487162850181 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2829 / 64 : ℚ) : ℝ) ∧
    Real.log ((2829 / 64 : ℚ) : ℝ) ≤ ((34126435895356273 / 9007199254740992 : ℚ) : ℝ) := by
  have hl : Real.exp ((273011487162850181 / 72057594037927936 : ℚ) : ℝ) ≤ ((2829 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2829 / 64 : ℚ) : ℝ) ≤ Real.exp ((34126435895356273 / 9007199254740992 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_987 : heightPower (987 : Fin 988) ≤ ((4461743028302173 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_987
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_987 : heightFactor (987 : Fin 988) ≤ ((2105215725 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_987
  obtain ⟨hpl, hph⟩ := kernel_bounds_2828
  obtain ⟨hcl, hch⟩ := kernel_bounds_2829
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2829
  have h : (((8003241 / 2048 : ℚ) : ℝ) * (logKernel ((707 / 16 : ℚ) : ℝ) - logKernel ((2829 / 64 : ℚ) : ℝ)) + ((256103712 / 31 : ℚ) : ℝ) * (heightZ ((2829 / 64 : ℚ) : ℝ)) ^ 2) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2829 / 64 : ℚ) : ℝ) + Real.log ((2829 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((2105215725 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

end LegendreK6.M2Pilot
