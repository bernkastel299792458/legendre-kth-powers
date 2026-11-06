import LegendreK6.M2PilotDefinitions
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp

/-! Generated proposals: every bound is checked by Lean, not by trusting Arb. -/
namespace LegendreK6.M2Pilot.Enclosures.Height005
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem height_z_bounds_2001 : ((734060921898369259 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2001 / 64 : ℚ) : ℝ) ∧
    heightZ ((2001 / 64 : ℚ) : ℝ) ≤ ((367030460949184631 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((734060921898369259 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2001 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-275 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2001 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-275 / 192 : ℚ) : ℝ) ≤ ((367030460949184631 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2001 : ((5919846144341685 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2001 / 64 : ℚ) : ℝ) ∧
    logKernel ((2001 / 64 : ℚ) : ℝ) ≤ ((2959923072170845 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2001
  constructor
  · exact (show ((5919846144341685 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((734060921898369259 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2001 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((367030460949184631 / 9223372036854775808 : ℚ) : ℝ) ≤ ((2959923072170845 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2002 : ((722680362153849911 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1001 / 32 : ℚ) : ℝ) ∧
    heightZ ((1001 / 32 : ℚ) : ℝ) ≤ ((361340181076924957 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((722680362153849911 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1001 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-139 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1001 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-139 / 96 : ℚ) : ℝ) ≤ ((361340181076924957 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2002 : ((2914033718362297 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((1001 / 32 : ℚ) : ℝ) ∧
    logKernel ((1001 / 32 : ℚ) : ℝ) ≤ ((5828067436724599 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2002
  constructor
  · exact (show ((2914033718362297 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((722680362153849911 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1001 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((361340181076924957 / 9223372036854775808 : ℚ) : ℝ) ≤ ((5828067436724599 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2003 : ((88934530204280429 / 2305843009213693952 : ℚ) : ℝ) ≤ heightZ ((2003 / 64 : ℚ) : ℝ) ∧
    heightZ ((2003 / 64 : ℚ) : ℝ) ≤ ((711476241634243435 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((88934530204280429 / 2305843009213693952 : ℚ) : ℝ) ≤ Real.exp (-((2003 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-281 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2003 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-281 / 192 : ℚ) : ℝ) ≤ ((711476241634243435 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2003 : ((2868855813041303 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2003 / 64 : ℚ) : ℝ) ∧
    logKernel ((2003 / 64 : ℚ) : ℝ) ≤ ((5737711626082611 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2003
  constructor
  · exact (show ((2868855813041303 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((88934530204280429 / 2305843009213693952 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2003 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((711476241634243435 / 18446744073709551616 : ℚ) : ℝ) ≤ ((5737711626082611 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2004 : ((700445824902911669 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((501 / 16 : ℚ) : ℝ) ∧
    heightZ ((501 / 16 : ℚ) : ℝ) ≤ ((87555728112863959 / 2305843009213693952 : ℚ) : ℝ) := by
  have h : ((700445824902911669 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((501 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-71 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((501 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-71 / 48 : ℚ) : ℝ) ≤ ((87555728112863959 / 2305843009213693952 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2004 : ((2824378326221417 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((501 / 16 : ℚ) : ℝ) ∧
    logKernel ((501 / 16 : ℚ) : ℝ) ≤ ((5648756652442839 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2004
  constructor
  · exact (show ((2824378326221417 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((700445824902911669 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((501 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((87555728112863959 / 2305843009213693952 : ℚ) : ℝ) ≤ ((5648756652442839 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2005 : ((43099151183264419 / 1152921504606846976 : ℚ) : ℝ) ≤ heightZ ((2005 / 64 : ℚ) : ℝ) ∧
    heightZ ((2005 / 64 : ℚ) : ℝ) ≤ ((689586418932230707 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((43099151183264419 / 1152921504606846976 : ℚ) : ℝ) ≤ Real.exp (-((2005 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-287 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2005 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-287 / 192 : ℚ) : ℝ) ≤ ((689586418932230707 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2005 : ((695147599730071 / 9007199254740992 : ℚ) : ℝ) ≤ logKernel ((2005 / 64 : ℚ) : ℝ) ∧
    logKernel ((2005 / 64 : ℚ) : ℝ) ≤ ((5561180797840573 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2005
  constructor
  · exact (show ((695147599730071 / 9007199254740992 : ℚ) : ℝ) ≤ zKernel ((43099151183264419 / 1152921504606846976 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2005 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((689586418932230707 / 18446744073709551616 : ℚ) : ℝ) ≤ ((5561180797840573 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2006 : ((169723843111525009 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((1003 / 32 : ℚ) : ℝ) ∧
    heightZ ((1003 / 32 : ℚ) : ℝ) ≤ ((678895372446100039 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((169723843111525009 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((1003 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-145 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1003 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-145 / 96 : ℚ) : ℝ) ≤ ((678895372446100039 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2006 : ((5474962681016933 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1003 / 32 : ℚ) : ℝ) ∧
    logKernel ((1003 / 32 : ℚ) : ℝ) ≤ ((2737481340508469 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2006
  constructor
  · exact (show ((5474962681016933 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((169723843111525009 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1003 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((678895372446100039 / 18446744073709551616 : ℚ) : ℝ) ≤ ((2737481340508469 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2007 : ((334185037636322601 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2007 / 64 : ℚ) : ℝ) ∧
    heightZ ((2007 / 64 : ℚ) : ℝ) ≤ ((668370075272645205 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((334185037636322601 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2007 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-293 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2007 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-293 / 192 : ℚ) : ℝ) ≤ ((668370075272645205 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2007 : ((5390081252198749 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2007 / 64 : ℚ) : ℝ) ∧
    logKernel ((2007 / 64 : ℚ) : ℝ) ≤ ((2695040626099377 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2007
  constructor
  · exact (show ((5390081252198749 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((334185037636322601 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2007 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((668370075272645205 / 18446744073709551616 : ℚ) : ℝ) ≤ ((2695040626099377 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2008 : ((658007957706955821 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((251 / 8 : ℚ) : ℝ) ∧
    heightZ ((251 / 8 : ℚ) : ℝ) ≤ ((41125497356684739 / 1152921504606846976 : ℚ) : ℝ) := by
  have h : ((658007957706955821 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((251 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-37 / 24 : ℚ) : ℝ) ∧
      Real.exp (-((251 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-37 / 24 : ℚ) : ℝ) ≤ ((41125497356684739 / 1152921504606846976 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2008 : ((5306515787959319 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((251 / 8 : ℚ) : ℝ) ∧
    logKernel ((251 / 8 : ℚ) : ℝ) ≤ ((1326628946989831 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2008
  constructor
  · exact (show ((5306515787959319 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((658007957706955821 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((251 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((41125497356684739 / 1152921504606846976 : ℚ) : ℝ) ≤ ((1326628946989831 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2009 : ((323903244941851735 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2009 / 64 : ℚ) : ℝ) ∧
    heightZ ((2009 / 64 : ℚ) : ℝ) ≤ ((647806489883703473 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((323903244941851735 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2009 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-299 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2009 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-299 / 192 : ℚ) : ℝ) ≤ ((647806489883703473 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2009 : ((326515367884931 / 4503599627370496 : ℚ) : ℝ) ≤ logKernel ((2009 / 64 : ℚ) : ℝ) ∧
    logKernel ((2009 / 64 : ℚ) : ℝ) ≤ ((5224245886158901 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2009
  constructor
  · exact (show ((326515367884931 / 4503599627370496 : ℚ) : ℝ) ≤ zKernel ((323903244941851735 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2009 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((647806489883703473 / 18446744073709551616 : ℚ) : ℝ) ≤ ((5224245886158901 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2010 : ((637763181159486211 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1005 / 32 : ℚ) : ℝ) ∧
    heightZ ((1005 / 32 : ℚ) : ℝ) ≤ ((318881590579743107 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((637763181159486211 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1005 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-151 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1005 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-151 / 96 : ℚ) : ℝ) ≤ ((318881590579743107 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2010 : ((1285812865240899 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((1005 / 32 : ℚ) : ℝ) ∧
    logKernel ((1005 / 32 : ℚ) : ℝ) ≤ ((5143251460963601 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2010
  constructor
  · exact (show ((1285812865240899 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((637763181159486211 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1005 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((318881590579743107 / 9223372036854775808 : ℚ) : ℝ) ≤ ((5143251460963601 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2011 : ((313937789752374493 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2011 / 64 : ℚ) : ℝ) ∧
    heightZ ((2011 / 64 : ℚ) : ℝ) ≤ ((627875579504748989 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((313937789752374493 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2011 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-305 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2011 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-305 / 192 : ℚ) : ℝ) ≤ ((627875579504748989 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2011 : ((2531756368970761 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2011 / 64 : ℚ) : ℝ) ∧
    logKernel ((2011 / 64 : ℚ) : ℝ) ≤ ((5063512737941527 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2011
  constructor
  · exact (show ((2531756368970761 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((313937789752374493 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2011 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((627875579504748989 / 18446744073709551616 : ℚ) : ℝ) ≤ ((5063512737941527 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2012 : ((618141270905131407 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((503 / 16 : ℚ) : ℝ) ∧
    heightZ ((503 / 16 : ℚ) : ℝ) ≤ ((309070635452565705 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((618141270905131407 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((503 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-77 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((503 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-77 / 48 : ℚ) : ℝ) ≤ ((309070635452565705 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2012 : ((311563140577183 / 4503599627370496 : ℚ) : ℝ) ≤ logKernel ((503 / 16 : ℚ) : ℝ) ∧
    logKernel ((503 / 16 : ℚ) : ℝ) ≤ ((4985010249234933 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2012
  constructor
  · exact (show ((311563140577183 / 4503599627370496 : ℚ) : ℝ) ≤ zKernel ((618141270905131407 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((503 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((309070635452565705 / 9223372036854775808 : ℚ) : ℝ) ≤ ((4985010249234933 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2013 : ((304278939386048397 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2013 / 64 : ℚ) : ℝ) ∧
    heightZ ((2013 / 64 : ℚ) : ℝ) ≤ ((608557878772096797 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((304278939386048397 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2013 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-311 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2013 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-311 / 192 : ℚ) : ℝ) ≤ ((608557878772096797 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2013 : ((2453862414403615 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2013 / 64 : ℚ) : ℝ) ∧
    logKernel ((2013 / 64 : ℚ) : ℝ) ≤ ((4907724828807235 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2013
  constructor
  · exact (show ((2453862414403615 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((304278939386048397 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2013 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((608557878772096797 / 18446744073709551616 : ℚ) : ℝ) ≤ ((4907724828807235 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2014 : ((599123063362698557 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1007 / 32 : ℚ) : ℝ) ∧
    heightZ ((1007 / 32 : ℚ) : ℝ) ≤ ((9361297865042165 / 288230376151711744 : ℚ) : ℝ) := by
  have h : ((599123063362698557 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1007 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-157 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1007 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-157 / 96 : ℚ) : ℝ) ≤ ((9361297865042165 / 288230376151711744 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2014 : ((301977350485231 / 4503599627370496 : ℚ) : ℝ) ≤ logKernel ((1007 / 32 : ℚ) : ℝ) ∧
    logKernel ((1007 / 32 : ℚ) : ℝ) ≤ ((4831637607763701 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2014
  constructor
  · exact (show ((301977350485231 / 4503599627370496 : ℚ) : ℝ) ≤ zKernel ((599123063362698557 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1007 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((9361297865042165 / 288230376151711744 : ℚ) : ℝ) ≤ ((4831637607763701 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2015 : ((589834521208342269 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2015 / 64 : ℚ) : ℝ) ∧
    heightZ ((2015 / 64 : ℚ) : ℝ) ≤ ((2304041098470087 / 72057594037927936 : ℚ) : ℝ) := by
  have h : ((589834521208342269 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2015 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-317 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2015 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-317 / 192 : ℚ) : ℝ) ≤ ((2304041098470087 / 72057594037927936 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2015 : ((4756730009744693 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2015 / 64 : ℚ) : ℝ) ∧
    logKernel ((2015 / 64 : ℚ) : ℝ) ≤ ((2378365004872349 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2015
  constructor
  · exact (show ((4756730009744693 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((589834521208342269 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2015 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((2304041098470087 / 72057594037927936 : ℚ) : ℝ) ≤ ((2378365004872349 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2016 : ((580689984552403963 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((63 / 2 : ℚ) : ℝ) ∧
    heightZ ((63 / 2 : ℚ) : ℝ) ≤ ((290344992276201983 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((580689984552403963 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((63 / 2 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-5 / 3 : ℚ) : ℝ) ∧
      Real.exp (-((63 / 2 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-5 / 3 : ℚ) : ℝ) ≤ ((290344992276201983 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2016 : ((292686484149397 / 4503599627370496 : ℚ) : ℝ) ≤ logKernel ((63 / 2 : ℚ) : ℝ) ∧
    logKernel ((63 / 2 : ℚ) : ℝ) ≤ ((4682983746390357 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2016
  constructor
  · exact (show ((292686484149397 / 4503599627370496 : ℚ) : ℝ) ≤ zKernel ((580689984552403963 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((63 / 2 : ℚ) : ℝ)) hh).trans
      (show zKernel ((290344992276201983 / 9223372036854775808 : ℚ) : ℝ) ≤ ((4682983746390357 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2017 : ((571687220796567349 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2017 / 64 : ℚ) : ℝ) ∧
    heightZ ((2017 / 64 : ℚ) : ℝ) ≤ ((71460902599570919 / 2305843009213693952 : ℚ) : ℝ) := by
  have h : ((571687220796567349 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2017 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-323 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2017 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-323 / 192 : ℚ) : ℝ) ≤ ((71460902599570919 / 2305843009213693952 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2017 : ((4610380812875541 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2017 / 64 : ℚ) : ℝ) ∧
    logKernel ((2017 / 64 : ℚ) : ℝ) ≤ ((2305190406437773 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2017
  constructor
  · exact (show ((4610380812875541 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((571687220796567349 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2017 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((71460902599570919 / 2305843009213693952 : ℚ) : ℝ) ≤ ((2305190406437773 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2018 : ((562824031955744773 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1009 / 32 : ℚ) : ℝ) ∧
    heightZ ((1009 / 32 : ℚ) : ℝ) ≤ ((70353003994468097 / 2305843009213693952 : ℚ) : ℝ) := by
  have h : ((562824031955744773 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1009 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-163 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1009 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-163 / 96 : ℚ) : ℝ) ≤ ((70353003994468097 / 2305843009213693952 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2018 : ((1134725870878517 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((1009 / 32 : ℚ) : ℝ) ∧
    logKernel ((1009 / 32 : ℚ) : ℝ) ≤ ((4538903483514073 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2018
  constructor
  · exact (show ((1134725870878517 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((562824031955744773 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1009 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((70353003994468097 / 2305843009213693952 : ℚ) : ℝ) ≤ ((4538903483514073 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2019 : ((138524563530362213 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((2019 / 64 : ℚ) : ℝ) ∧
    heightZ ((2019 / 64 : ℚ) : ℝ) ≤ ((554098254121448855 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((138524563530362213 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((2019 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-329 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2019 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-329 / 192 : ℚ) : ℝ) ≤ ((554098254121448855 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2019 : ((4468534307431037 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2019 / 64 : ℚ) : ℝ) ∧
    logKernel ((2019 / 64 : ℚ) : ℝ) ≤ ((2234267153715521 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2019
  constructor
  · exact (show ((4468534307431037 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((138524563530362213 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2019 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((554098254121448855 / 18446744073709551616 : ℚ) : ℝ) ≤ ((2234267153715521 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2020 : ((136376939233370937 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((505 / 16 : ℚ) : ℝ) ∧
    heightZ ((505 / 16 : ℚ) : ℝ) ≤ ((545507756933483751 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((136376939233370937 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((505 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-83 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((505 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-83 / 48 : ℚ) : ℝ) ≤ ((545507756933483751 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2020 : ((2199628052151143 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((505 / 16 : ℚ) : ℝ) ∧
    logKernel ((505 / 16 : ℚ) : ℝ) ≤ ((4399256104302291 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2020
  constructor
  · exact (show ((2199628052151143 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((136376939233370937 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((505 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((545507756933483751 / 18446744073709551616 : ℚ) : ℝ) ≤ ((4399256104302291 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2021 : ((537050443059827123 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2021 / 64 : ℚ) : ℝ) ∧
    heightZ ((2021 / 64 : ℚ) : ℝ) ≤ ((268525221529913563 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((537050443059827123 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2021 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-335 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2021 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-335 / 192 : ℚ) : ℝ) ≤ ((268525221529913563 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2021 : ((2165525980079947 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2021 / 64 : ℚ) : ℝ) ∧
    logKernel ((2021 / 64 : ℚ) : ℝ) ≤ ((4331051960159899 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2021
  constructor
  · exact (show ((2165525980079947 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((537050443059827123 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2021 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((268525221529913563 / 9223372036854775808 : ℚ) : ℝ) ≤ ((4331051960159899 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2022 : ((528724247684575767 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1011 / 32 : ℚ) : ℝ) ∧
    heightZ ((1011 / 32 : ℚ) : ℝ) ≤ ((264362123842287885 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((528724247684575767 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1011 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-169 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1011 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-169 / 96 : ℚ) : ℝ) ≤ ((264362123842287885 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2022 : ((4263905223262705 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1011 / 32 : ℚ) : ℝ) ∧
    logKernel ((1011 / 32 : ℚ) : ℝ) ≤ ((2131952611631355 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2022
  constructor
  · exact (show ((4263905223262705 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((528724247684575767 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1011 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((264362123842287885 / 9223372036854775808 : ℚ) : ℝ) ≤ ((2131952611631355 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2023 : ((260263569001914949 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2023 / 64 : ℚ) : ℝ) ∧
    heightZ ((2023 / 64 : ℚ) : ℝ) ≤ ((520527138003829901 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((260263569001914949 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2023 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-341 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2023 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-341 / 192 : ℚ) : ℝ) ≤ ((520527138003829901 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2023 : ((1049449875007721 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((2023 / 64 : ℚ) : ℝ) ∧
    logKernel ((2023 / 64 : ℚ) : ℝ) ≤ ((4197799500030889 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2023
  constructor
  · exact (show ((1049449875007721 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((260263569001914949 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2023 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((520527138003829901 / 18446744073709551616 : ℚ) : ℝ) ≤ ((4197799500030889 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2024 : ((512457112729393049 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((253 / 8 : ℚ) : ℝ) ∧
    heightZ ((253 / 8 : ℚ) : ℝ) ≤ ((128114278182348263 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((512457112729393049 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((253 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-43 / 24 : ℚ) : ℝ) ∧
      Real.exp (-((253 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-43 / 24 : ℚ) : ℝ) ≤ ((128114278182348263 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2024 : ((2066359325521745 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((253 / 8 : ℚ) : ℝ) ∧
    logKernel ((253 / 8 : ℚ) : ℝ) ≤ ((4132718651043495 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2024
  constructor
  · exact (show ((2066359325521745 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((512457112729393049 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((253 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((128114278182348263 / 4611686018427387904 : ℚ) : ℝ) ≤ ((4132718651043495 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2025 : ((252256100800083189 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2025 / 64 : ℚ) : ℝ) ∧
    heightZ ((2025 / 64 : ℚ) : ℝ) ≤ ((504512201600166381 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((252256100800083189 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2025 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-347 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2025 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-347 / 192 : ℚ) : ℝ) ≤ ((504512201600166381 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2025 : ((4068646787098113 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2025 / 64 : ℚ) : ℝ) ∧
    logKernel ((2025 / 64 : ℚ) : ℝ) ≤ ((2034323393549059 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2025
  constructor
  · exact (show ((4068646787098113 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((252256100800083189 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2025 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((504512201600166381 / 18446744073709551616 : ℚ) : ℝ) ≤ ((2034323393549059 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2026 : ((496690464901118105 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1013 / 32 : ℚ) : ℝ) ∧
    heightZ ((1013 / 32 : ℚ) : ℝ) ≤ ((124172616225279527 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((496690464901118105 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1013 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-175 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1013 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-175 / 96 : ℚ) : ℝ) ≤ ((124172616225279527 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2026 : ((4005568265331595 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1013 / 32 : ℚ) : ℝ) ∧
    logKernel ((1013 / 32 : ℚ) : ℝ) ≤ ((250348016583225 / 4503599627370496 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2026
  constructor
  · exact (show ((4005568265331595 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((496690464901118105 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1013 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((124172616225279527 / 4611686018427387904 : ℚ) : ℝ) ≤ ((250348016583225 / 4503599627370496 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2027 : ((488989992989710635 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2027 / 64 : ℚ) : ℝ) ∧
    heightZ ((2027 / 64 : ℚ) : ℝ) ≤ ((244494996494855319 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((488989992989710635 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2027 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-353 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2027 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-353 / 192 : ℚ) : ℝ) ≤ ((244494996494855319 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2027 : ((1971733842700445 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2027 / 64 : ℚ) : ℝ) ∧
    logKernel ((2027 / 64 : ℚ) : ℝ) ≤ ((3943467685400895 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2027
  constructor
  · exact (show ((1971733842700445 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((488989992989710635 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2027 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((244494996494855319 / 9223372036854775808 : ℚ) : ℝ) ≤ ((3943467685400895 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2028 : ((240704452914834877 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((507 / 16 : ℚ) : ℝ) ∧
    heightZ ((507 / 16 : ℚ) : ℝ) ≤ ((481408905829669757 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((240704452914834877 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((507 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-89 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((507 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-89 / 48 : ℚ) : ℝ) ≤ ((481408905829669757 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2028 : ((3882329885723141 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((507 / 16 : ℚ) : ℝ) ∧
    logKernel ((507 / 16 : ℚ) : ℝ) ≤ ((1941164942861573 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2028
  constructor
  · exact (show ((3882329885723141 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((240704452914834877 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((507 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((481408905829669757 / 18446744073709551616 : ℚ) : ℝ) ≤ ((1941164942861573 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2029 : ((473945352531982057 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2029 / 64 : ℚ) : ℝ) ∧
    heightZ ((2029 / 64 : ℚ) : ℝ) ≤ ((118486338132995515 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((473945352531982057 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2029 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-359 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2029 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-359 / 192 : ℚ) : ℝ) ≤ ((118486338132995515 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2029 : ((1911069969887023 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2029 / 64 : ℚ) : ℝ) ∧
    logKernel ((2029 / 64 : ℚ) : ℝ) ≤ ((3822139939774051 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2029
  constructor
  · exact (show ((1911069969887023 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((473945352531982057 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2029 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((118486338132995515 / 4611686018427387904 : ℚ) : ℝ) ≤ ((3822139939774051 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2030 : ((58324688862876069 / 2305843009213693952 : ℚ) : ℝ) ≤ heightZ ((1015 / 32 : ℚ) : ℝ) ∧
    heightZ ((1015 / 32 : ℚ) : ℝ) ≤ ((466597510903008555 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((58324688862876069 / 2305843009213693952 : ℚ) : ℝ) ≤ Real.exp (-((1015 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-181 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1015 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-181 / 96 : ℚ) : ℝ) ≤ ((466597510903008555 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2030 : ((3762883152443615 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1015 / 32 : ℚ) : ℝ) ∧
    logKernel ((1015 / 32 : ℚ) : ℝ) ≤ ((940720788110905 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2030
  constructor
  · exact (show ((3762883152443615 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((58324688862876069 / 2305843009213693952 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1015 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((466597510903008555 / 18446744073709551616 : ℚ) : ℝ) ≤ ((940720788110905 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2031 : ((459363586999604121 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2031 / 64 : ℚ) : ℝ) ∧
    heightZ ((2031 / 64 : ℚ) : ℝ) ≤ ((114840896749901031 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((459363586999604121 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2031 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-365 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2031 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-365 / 192 : ℚ) : ℝ) ≤ ((114840896749901031 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2031 : ((1852272528224209 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2031 / 64 : ℚ) : ℝ) ∧
    logKernel ((2031 / 64 : ℚ) : ℝ) ≤ ((3704545056448423 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2031
  constructor
  · exact (show ((1852272528224209 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((459363586999604121 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2031 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((114840896749901031 / 4611686018427387904 : ℚ) : ℝ) ≤ ((3704545056448423 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2032 : ((226120907345567101 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((127 / 4 : ℚ) : ℝ) ∧
    heightZ ((127 / 4 : ℚ) : ℝ) ≤ ((452241814691134205 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((226120907345567101 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((127 / 4 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-23 / 12 : ℚ) : ℝ) ∧
      Real.exp (-((127 / 4 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-23 / 12 : ℚ) : ℝ) ≤ ((452241814691134205 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2032 : ((3647111408799467 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((127 / 4 : ℚ) : ℝ) ∧
    logKernel ((127 / 4 : ℚ) : ℝ) ≤ ((227944463049967 / 4503599627370496 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2032
  constructor
  · exact (show ((3647111408799467 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((226120907345567101 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((127 / 4 : ℚ) : ℝ)) hh).trans
      (show zKernel ((452241814691134205 / 18446744073709551616 : ℚ) : ℝ) ≤ ((227944463049967 / 4503599627370496 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2033 : ((445230455228281785 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2033 / 64 : ℚ) : ℝ) ∧
    heightZ ((2033 / 64 : ℚ) : ℝ) ≤ ((111307613807070447 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((445230455228281785 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2033 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-371 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2033 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-371 / 192 : ℚ) : ℝ) ≤ ((111307613807070447 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2033 : ((3590568187324851 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2033 / 64 : ℚ) : ℝ) ∧
    logKernel ((2033 / 64 : ℚ) : ℝ) ≤ ((448821023415607 / 9007199254740992 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2033
  constructor
  · exact (show ((3590568187324851 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((445230455228281785 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2033 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((111307613807070447 / 4611686018427387904 : ℚ) : ℝ) ≤ ((448821023415607 / 9007199254740992 : ℚ) : ℝ) by norm_num [zKernel])

theorem log_height_bounds_160 : ((124047828234438101 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((1001 / 32 : ℚ) : ℝ) ∧
    Real.log ((1001 / 32 : ℚ) : ℝ) ≤ ((248095656468876205 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((124047828234438101 / 36028797018963968 : ℚ) : ℝ) ≤ ((1001 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1001 / 32 : ℚ) : ℝ) ≤ Real.exp ((248095656468876205 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_160 : heightPower (160 : Fin 988) ≤ ((727231099970829 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_160
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_160 : heightFactor (160 : Fin 988) ≤ ((207506133969103 / 35184372088832 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_160
  obtain ⟨hpl, hph⟩ := kernel_bounds_2001
  obtain ⟨hcl, hch⟩ := kernel_bounds_2002
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2002
  have h : (((1002001 / 512 : ℚ) : ℝ) * (logKernel ((2001 / 64 : ℚ) : ℝ) - logKernel ((1001 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1001 / 32 : ℚ) : ℝ) + Real.log ((1001 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((207506133969103 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_161 : ((248131640286871399 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2003 / 64 : ℚ) : ℝ) ∧
    Real.log ((2003 / 64 : ℚ) : ℝ) ≤ ((124065820143435701 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((248131640286871399 / 72057594037927936 : ℚ) : ℝ) ≤ ((2003 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2003 / 64 : ℚ) : ℝ) ≤ Real.exp ((124065820143435701 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_161 : heightPower (161 : Fin 988) ≤ ((731769708270977 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_161
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_161 : heightFactor (161 : Fin 988) ≤ ((1644762022765659 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_161
  obtain ⟨hpl, hph⟩ := kernel_bounds_2002
  obtain ⟨hcl, hch⟩ := kernel_bounds_2003
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2003
  have h : (((4012009 / 2048 : ℚ) : ℝ) * (logKernel ((1001 / 32 : ℚ) : ℝ) - logKernel ((2003 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2003 / 64 : ℚ) : ℝ) + Real.log ((2003 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1644762022765659 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_162 : ((248167606144387689 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((501 / 16 : ℚ) : ℝ) ∧
    Real.log ((501 / 16 : ℚ) : ℝ) ≤ ((62041901536096923 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((248167606144387689 / 72057594037927936 : ℚ) : ℝ) ≤ ((501 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((501 / 16 : ℚ) : ℝ) ≤ Real.exp ((62041901536096923 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_162 : heightPower (162 : Fin 988) ≤ ((184077061603251 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_162
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_162 : heightFactor (162 : Fin 988) ≤ ((1629614801291187 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_162
  obtain ⟨hpl, hph⟩ := kernel_bounds_2003
  obtain ⟨hcl, hch⟩ := kernel_bounds_2004
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2004
  have h : (((251001 / 128 : ℚ) : ℝ) * (logKernel ((2003 / 64 : ℚ) : ℝ) - logKernel ((501 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((501 / 16 : ℚ) : ℝ) + Real.log ((501 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1629614801291187 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_163 : ((15512722128709077 / 4503599627370496 : ℚ) : ℝ) ≤ Real.log ((2005 / 64 : ℚ) : ℝ) ∧
    Real.log ((2005 / 64 : ℚ) : ℝ) ≤ ((248203554059345235 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((15512722128709077 / 4503599627370496 : ℚ) : ℝ) ≤ ((2005 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2005 / 64 : ℚ) : ℝ) ≤ Real.exp ((248203554059345235 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_163 : heightPower (163 : Fin 988) ≤ ((740846714466911 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_163
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_163 : heightFactor (163 : Fin 988) ≤ ((1614606138080811 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_163
  obtain ⟨hpl, hph⟩ := kernel_bounds_2004
  obtain ⟨hcl, hch⟩ := kernel_bounds_2005
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2005
  have h : (((4020025 / 2048 : ℚ) : ℝ) * (logKernel ((501 / 16 : ℚ) : ℝ) - logKernel ((2005 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2005 / 64 : ℚ) : ℝ) + Real.log ((2005 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1614606138080811 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_164 : ((124119742024818691 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((1003 / 32 : ℚ) : ℝ) ∧
    Real.log ((1003 / 32 : ℚ) : ℝ) ≤ ((248239484049637385 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((124119742024818691 / 36028797018963968 : ℚ) : ℝ) ≤ ((1003 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1003 / 32 : ℚ) : ℝ) ≤ Real.exp ((248239484049637385 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_164 : heightPower (164 : Fin 988) ≤ ((372692556251297 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_164
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_164 : heightFactor (164 : Fin 988) ≤ ((1599734775307365 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_164
  obtain ⟨hpl, hph⟩ := kernel_bounds_2005
  obtain ⟨hcl, hch⟩ := kernel_bounds_2006
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2006
  have h : (((1006009 / 512 : ℚ) : ℝ) * (logKernel ((2005 / 64 : ℚ) : ℝ) - logKernel ((1003 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1003 / 32 : ℚ) : ℝ) + Real.log ((1003 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1599734775307365 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_165 : ((248275396133130737 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2007 / 64 : ℚ) : ℝ) ∧
    Real.log ((2007 / 64 : ℚ) : ℝ) ≤ ((62068849033282685 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((248275396133130737 / 72057594037927936 : ℚ) : ℝ) ≤ ((2007 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2007 / 64 : ℚ) : ℝ) ≤ Real.exp ((62068849033282685 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_165 : heightPower (165 : Fin 988) ≤ ((749923440589843 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_165
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_165 : heightFactor (165 : Fin 988) ≤ ((792499733231681 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_165
  obtain ⟨hpl, hph⟩ := kernel_bounds_2006
  obtain ⟨hcl, hch⟩ := kernel_bounds_2007
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2007
  have h : (((4028049 / 2048 : ℚ) : ℝ) * (logKernel ((1003 / 32 : ℚ) : ℝ) - logKernel ((2007 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2007 / 64 : ℚ) : ℝ) + Real.log ((2007 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((792499733231681 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_166 : ((248311290327665199 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((251 / 8 : ℚ) : ℝ) ∧
    Real.log ((251 / 8 : ℚ) : ℝ) ≤ ((124155645163832601 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((248311290327665199 / 72057594037927936 : ℚ) : ℝ) ≤ ((251 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((251 / 8 : ℚ) : ℝ) ≤ Real.exp ((124155645163832601 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_166 : heightPower (166 : Fin 988) ≤ ((188615424699587 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_166
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_166 : heightFactor (166 : Fin 988) ≤ ((1570398976260143 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_166
  obtain ⟨hpl, hph⟩ := kernel_bounds_2007
  obtain ⟨hcl, hch⟩ := kernel_bounds_2008
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2008
  have h : (((63001 / 32 : ℚ) : ℝ) * (logKernel ((2007 / 64 : ℚ) : ℝ) - logKernel ((251 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((251 / 8 : ℚ) : ℝ) + Real.log ((251 / 8 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1570398976260143 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_167 : ((62086791662763505 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((2009 / 64 : ℚ) : ℝ) ∧
    Real.log ((2009 / 64 : ℚ) : ℝ) ≤ ((248347166651054023 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((62086791662763505 / 18014398509481984 : ℚ) : ℝ) ≤ ((2009 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2009 / 64 : ℚ) : ℝ) ≤ Real.exp ((248347166651054023 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_167 : heightPower (167 : Fin 988) ≤ ((758999887197689 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_167
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_167 : heightFactor (167 : Fin 988) ≤ ((777966040263953 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_167
  obtain ⟨hpl, hph⟩ := kernel_bounds_2008
  obtain ⟨hcl, hch⟩ := kernel_bounds_2009
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2009
  have h : (((4036081 / 2048 : ℚ) : ℝ) * (logKernel ((251 / 8 : ℚ) : ℝ) - logKernel ((2009 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2009 / 64 : ℚ) : ℝ) + Real.log ((2009 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((777966040263953 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_168 : ((124191512560541931 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((1005 / 32 : ℚ) : ℝ) ∧
    Real.log ((1005 / 32 : ℚ) : ℝ) ≤ ((248383025121083865 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((124191512560541931 / 36028797018963968 : ℚ) : ℝ) ≤ ((1005 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1005 / 32 : ℚ) : ℝ) ≤ Real.exp ((248383025121083865 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_168 : heightPower (168 : Fin 988) ≤ ((763538005857347 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_168
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_168 : heightFactor (168 : Fin 988) ≤ ((1541597566116623 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_168
  obtain ⟨hpl, hph⟩ := kernel_bounds_2009
  obtain ⟨hcl, hch⟩ := kernel_bounds_2010
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2010
  have h : (((1010025 / 512 : ℚ) : ℝ) * (logKernel ((2009 / 64 : ℚ) : ℝ) - logKernel ((1005 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1005 / 32 : ℚ) : ℝ) + Real.log ((1005 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1541597566116623 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_169 : ((62104716438878711 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((2011 / 64 : ℚ) : ℝ) ∧
    Real.log ((2011 / 64 : ℚ) : ℝ) ≤ ((248418865755514847 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((62104716438878711 / 18014398509481984 : ℚ) : ℝ) ≤ ((2011 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2011 / 64 : ℚ) : ℝ) ≤ Real.exp ((248418865755514847 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_169 : heightPower (169 : Fin 988) ≤ ((768076054846697 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_169
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_169 : heightFactor (169 : Fin 988) ≤ ((763697115398913 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_169
  obtain ⟨hpl, hph⟩ := kernel_bounds_2010
  obtain ⟨hcl, hch⟩ := kernel_bounds_2011
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2011
  have h : (((4044121 / 2048 : ℚ) : ℝ) * (logKernel ((1005 / 32 : ℚ) : ℝ) - logKernel ((2011 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2011 / 64 : ℚ) : ℝ) + Real.log ((2011 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((763697115398913 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_170 : ((248454688572080597 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((503 / 16 : ℚ) : ℝ) ∧
    Real.log ((503 / 16 : ℚ) : ℝ) ≤ ((31056836071510075 / 9007199254740992 : ℚ) : ℝ) := by
  have hl : Real.exp ((248454688572080597 / 72057594037927936 : ℚ) : ℝ) ≤ ((503 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((503 / 16 : ℚ) : ℝ) ≤ Real.exp ((31056836071510075 / 9007199254740992 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_170 : heightPower (170 : Fin 988) ≤ ((772614034235011 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_170
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_170 : heightFactor (170 : Fin 988) ≤ ((1513320883167259 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_170
  obtain ⟨hpl, hph⟩ := kernel_bounds_2011
  obtain ⟨hcl, hch⟩ := kernel_bounds_2012
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2012
  have h : (((253009 / 128 : ℚ) : ℝ) * (logKernel ((2011 / 64 : ℚ) : ℝ) - logKernel ((503 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((503 / 16 : ℚ) : ℝ) + Real.log ((503 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1513320883167259 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_171 : ((248490493588488317 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2013 / 64 : ℚ) : ℝ) ∧
    Real.log ((2013 / 64 : ℚ) : ℝ) ≤ ((1941331981160065 / 562949953421312 : ℚ) : ℝ) := by
  have hl : Real.exp ((248490493588488317 / 72057594037927936 : ℚ) : ℝ) ≤ ((2013 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2013 / 64 : ℚ) : ℝ) ≤ Real.exp ((1941331981160065 / 562949953421312 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_171 : heightPower (171 : Fin 988) ≤ ((388575972045729 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_171
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_171 : heightFactor (171 : Fin 988) ≤ ((749688171274193 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_171
  obtain ⟨hpl, hph⟩ := kernel_bounds_2012
  obtain ⟨hcl, hch⟩ := kernel_bounds_2013
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2013
  have h : (((4052169 / 2048 : ℚ) : ℝ) * (logKernel ((503 / 16 : ℚ) : ℝ) - logKernel ((2013 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2013 / 64 : ℚ) : ℝ) + Real.log ((2013 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((749688171274193 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_172 : ((248526280822418819 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1007 / 32 : ℚ) : ℝ) ∧
    Real.log ((1007 / 32 : ℚ) : ℝ) ≤ ((124263140411209411 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((248526280822418819 / 72057594037927936 : ℚ) : ℝ) ≤ ((1007 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1007 / 32 : ℚ) : ℝ) ≤ Real.exp ((124263140411209411 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_172 : heightPower (172 : Fin 988) ≤ ((781689784485103 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_172
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_172 : heightFactor (172 : Fin 988) ≤ ((742779719448377 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_172
  obtain ⟨hpl, hph⟩ := kernel_bounds_2013
  obtain ⟨hcl, hch⟩ := kernel_bounds_2014
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2014
  have h : (((1014049 / 512 : ℚ) : ℝ) * (logKernel ((2013 / 64 : ℚ) : ℝ) - logKernel ((1007 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1007 / 32 : ℚ) : ℝ) + Real.log ((1007 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((742779719448377 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_173 : ((248562050291526585 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2015 / 64 : ℚ) : ℝ) ∧
    Real.log ((2015 / 64 : ℚ) : ℝ) ≤ ((62140512572881647 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((248562050291526585 / 72057594037927936 : ℚ) : ℝ) ≤ ((2015 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2015 / 64 : ℚ) : ℝ) ≤ Real.exp ((62140512572881647 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_173 : heightPower (173 : Fin 988) ≤ ((786227555484909 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_173
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_173 : heightFactor (173 : Fin 988) ≤ ((183983626588149 / 35184372088832 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_173
  obtain ⟨hpl, hph⟩ := kernel_bounds_2014
  obtain ⟨hcl, hch⟩ := kernel_bounds_2015
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2015
  have h : (((4060225 / 2048 : ℚ) : ℝ) * (logKernel ((1007 / 32 : ℚ) : ℝ) - logKernel ((2015 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2015 / 64 : ℚ) : ℝ) + Real.log ((2015 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((183983626588149 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_174 : ((248597802013439821 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((63 / 2 : ℚ) : ℝ) ∧
    Real.log ((63 / 2 : ℚ) : ℝ) ≤ ((15537362625839989 / 4503599627370496 : ℚ) : ℝ) := by
  have hl : Real.exp ((248597802013439821 / 72057594037927936 : ℚ) : ℝ) ≤ ((63 / 2 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((63 / 2 : ℚ) : ℝ) ≤ Real.exp ((15537362625839989 / 4503599627370496 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_174 : heightPower (174 : Fin 988) ≤ ((790765257159737 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_174
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_174 : heightFactor (174 : Fin 988) ≤ ((364575978727463 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_174
  obtain ⟨hpl, hph⟩ := kernel_bounds_2015
  obtain ⟨hcl, hch⟩ := kernel_bounds_2016
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2016
  have h : (((3969 / 2 : ℚ) : ℝ) * (logKernel ((2015 / 64 : ℚ) : ℝ) - logKernel ((63 / 2 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((63 / 2 : ℚ) : ℝ) + Real.log ((63 / 2 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((364575978727463 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_175 : ((124316768002880253 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2017 / 64 : ℚ) : ℝ) ∧
    Real.log ((2017 / 64 : ℚ) : ℝ) ≤ ((248633536005760509 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((124316768002880253 / 36028797018963968 : ℚ) : ℝ) ≤ ((2017 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2017 / 64 : ℚ) : ℝ) ≤ Real.exp ((248633536005760509 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_175 : heightPower (175 : Fin 988) ≤ ((795302889578343 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_175
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_175 : heightFactor (175 : Fin 988) ≤ ((1444863006797073 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_175
  obtain ⟨hpl, hph⟩ := kernel_bounds_2016
  obtain ⟨hcl, hch⟩ := kernel_bounds_2017
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2017
  have h : (((4068289 / 2048 : ℚ) : ℝ) * (logKernel ((63 / 2 : ℚ) : ℝ) - logKernel ((2017 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2017 / 64 : ℚ) : ℝ) + Real.log ((2017 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1444863006797073 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_176 : ((248669252286064445 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1009 / 32 : ℚ) : ℝ) ∧
    Real.log ((1009 / 32 : ℚ) : ℝ) ≤ ((3885457066969757 / 1125899906842624 : ℚ) : ℝ) := by
  have hl : Real.exp ((248669252286064445 / 72057594037927936 : ℚ) : ℝ) ≤ ((1009 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1009 / 32 : ℚ) : ℝ) ≤ Real.exp ((3885457066969757 / 1125899906842624 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_176 : heightPower (176 : Fin 988) ≤ ((799840452809385 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_176
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_176 : heightFactor (176 : Fin 988) ≤ ((715772579955535 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_176
  obtain ⟨hpl, hph⟩ := kernel_bounds_2017
  obtain ⟨hcl, hch⟩ := kernel_bounds_2018
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2018
  have h : (((1018081 / 512 : ℚ) : ℝ) * (logKernel ((2017 / 64 : ℚ) : ℝ) - logKernel ((1009 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1009 / 32 : ℚ) : ℝ) + Real.log ((1009 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((715772579955535 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_177 : ((124352475435950661 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2019 / 64 : ℚ) : ℝ) ∧
    Real.log ((2019 / 64 : ℚ) : ℝ) ≤ ((248704950871901325 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((124352475435950661 / 36028797018963968 : ℚ) : ℝ) ≤ ((2019 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2019 / 64 : ℚ) : ℝ) ≤ Real.exp ((248704950871901325 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_177 : heightPower (177 : Fin 988) ≤ ((402188973460707 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_177
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_177 : heightFactor (177 : Fin 988) ≤ ((1418349255962435 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_177
  obtain ⟨hpl, hph⟩ := kernel_bounds_2018
  obtain ⟨hcl, hch⟩ := kernel_bounds_2019
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2019
  have h : (((4076361 / 2048 : ℚ) : ℝ) * (logKernel ((1009 / 32 : ℚ) : ℝ) - logKernel ((2019 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2019 / 64 : ℚ) : ℝ) + Real.log ((2019 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1418349255962435 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_178 : ((124370315890397375 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((505 / 16 : ℚ) : ℝ) ∧
    Real.log ((505 / 16 : ℚ) : ℝ) ≤ ((248740631780794753 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((124370315890397375 / 36028797018963968 : ℚ) : ℝ) ≤ ((505 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((505 / 16 : ℚ) : ℝ) ≤ Real.exp ((248740631780794753 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_178 : heightPower (178 : Fin 988) ≤ ((808915371982883 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_178
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_178 : heightFactor (178 : Fin 988) ≤ ((1405274186737445 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_178
  obtain ⟨hpl, hph⟩ := kernel_bounds_2019
  obtain ⟨hcl, hch⟩ := kernel_bounds_2020
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2020
  have h : (((255025 / 128 : ℚ) : ℝ) * (logKernel ((2019 / 64 : ℚ) : ℝ) - logKernel ((505 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((505 / 16 : ℚ) : ℝ) + Real.log ((505 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1405274186737445 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_179 : ((124388147515121161 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2021 / 64 : ℚ) : ℝ) ∧
    Real.log ((2021 / 64 : ℚ) : ℝ) ≤ ((248776295030242325 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((124388147515121161 / 36028797018963968 : ℚ) : ℝ) ≤ ((2021 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2021 / 64 : ℚ) : ℝ) ≤ Real.exp ((248776295030242325 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_179 : heightPower (179 : Fin 988) ≤ ((406726364031071 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_179
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_179 : heightFactor (179 : Fin 988) ≤ ((696159427004085 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_179
  obtain ⟨hpl, hph⟩ := kernel_bounds_2020
  obtain ⟨hcl, hch⟩ := kernel_bounds_2021
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2021
  have h : (((4084441 / 2048 : ℚ) : ℝ) * (logKernel ((505 / 16 : ℚ) : ℝ) - logKernel ((2021 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2021 / 64 : ℚ) : ℝ) + Real.log ((2021 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((696159427004085 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_180 : ((248811940637715667 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1011 / 32 : ℚ) : ℝ) ∧
    Real.log ((1011 / 32 : ℚ) : ℝ) ≤ ((124405970318857835 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((248811940637715667 / 72057594037927936 : ℚ) : ℝ) ≤ ((1011 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1011 / 32 : ℚ) : ℝ) ≤ Real.exp ((124405970318857835 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_180 : heightPower (180 : Fin 988) ≤ ((408995007613719 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_180
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_180 : heightFactor (180 : Fin 988) ≤ ((689741084721687 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_180
  obtain ⟨hpl, hph⟩ := kernel_bounds_2021
  obtain ⟨hcl, hch⟩ := kernel_bounds_2022
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2022
  have h : (((1022121 / 512 : ℚ) : ℝ) * (logKernel ((2021 / 64 : ℚ) : ℝ) - logKernel ((1011 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1011 / 32 : ℚ) : ℝ) + Real.log ((1011 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((689741084721687 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_181 : ((124423784310330247 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2023 / 64 : ℚ) : ℝ) ∧
    Real.log ((2023 / 64 : ℚ) : ℝ) ≤ ((248847568620660497 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((124423784310330247 / 36028797018963968 : ℚ) : ℝ) ≤ ((2023 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2023 / 64 : ℚ) : ℝ) ≤ Real.exp ((248847568620660497 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_181 : heightPower (181 : Fin 988) ≤ ((822527233546921 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_181
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_181 : heightFactor (181 : Fin 988) ≤ ((1366763054520199 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_181
  obtain ⟨hpl, hph⟩ := kernel_bounds_2022
  obtain ⟨hcl, hch⟩ := kernel_bounds_2023
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2023
  have h : (((4092529 / 2048 : ℚ) : ℝ) * (logKernel ((1011 / 32 : ℚ) : ℝ) - logKernel ((2023 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2023 / 64 : ℚ) : ℝ) + Real.log ((2023 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1366763054520199 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_182 : ((124441589498248325 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((253 / 8 : ℚ) : ℝ) ∧
    Real.log ((253 / 8 : ℚ) : ℝ) ≤ ((248883178996496653 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((124441589498248325 / 36028797018963968 : ℚ) : ℝ) ≤ ((253 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((253 / 8 : ℚ) : ℝ) ≤ Real.exp ((248883178996496653 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_182 : heightPower (182 : Fin 988) ≤ ((827064383088635 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_182
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_182 : heightFactor (182 : Fin 988) ≤ ((338540110109159 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_182
  obtain ⟨hpl, hph⟩ := kernel_bounds_2023
  obtain ⟨hcl, hch⟩ := kernel_bounds_2024
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2024
  have h : (((64009 / 32 : ℚ) : ℝ) * (logKernel ((2023 / 64 : ℚ) : ℝ) - logKernel ((253 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((253 / 8 : ℚ) : ℝ) + Real.log ((253 / 8 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((338540110109159 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_183 : ((31114846472827271 / 9007199254740992 : ℚ) : ℝ) ≤ Real.log ((2025 / 64 : ℚ) : ℝ) ∧
    Real.log ((2025 / 64 : ℚ) : ℝ) ≤ ((248918771782618171 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((31114846472827271 / 9007199254740992 : ℚ) : ℝ) ≤ ((2025 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2025 / 64 : ℚ) : ℝ) ≤ Real.exp ((248918771782618171 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_183 : heightPower (183 : Fin 988) ≤ ((415800731960263 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_183
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_183 : heightFactor (183 : Fin 988) ≤ ((1341673268024759 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_183
  obtain ⟨hpl, hph⟩ := kernel_bounds_2024
  obtain ⟨hcl, hch⟩ := kernel_bounds_2025
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2025
  have h : (((4100625 / 2048 : ℚ) : ℝ) * (logKernel ((253 / 8 : ℚ) : ℝ) - logKernel ((2025 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2025 / 64 : ℚ) : ℝ) + Real.log ((2025 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1341673268024759 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_184 : ((124477173498196659 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((1013 / 32 : ℚ) : ℝ) ∧
    Real.log ((1013 / 32 : ℚ) : ℝ) ≤ ((248954346996393321 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((124477173498196659 / 36028797018963968 : ℚ) : ℝ) ≤ ((1013 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1013 / 32 : ℚ) : ℝ) ≤ Real.exp ((248954346996393321 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_184 : heightPower (184 : Fin 988) ≤ ((836138476110439 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_184
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_184 : heightFactor (184 : Fin 988) ≤ ((1329300487664731 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_184
  obtain ⟨hpl, hph⟩ := kernel_bounds_2025
  obtain ⟨hcl, hch⟩ := kernel_bounds_2026
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2026
  have h : (((1026169 / 512 : ℚ) : ℝ) * (logKernel ((2025 / 64 : ℚ) : ℝ) - logKernel ((1013 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1013 / 32 : ℚ) : ℝ) + Real.log ((1013 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1329300487664731 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_185 : ((248989904655164659 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2027 / 64 : ℚ) : ℝ) ∧
    Real.log ((2027 / 64 : ℚ) : ℝ) ≤ ((124494952327582331 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((248989904655164659 / 72057594037927936 : ℚ) : ℝ) ≤ ((2027 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2027 / 64 : ℚ) : ℝ) ≤ Real.exp ((124494952327582331 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_185 : heightPower (185 : Fin 988) ≤ ((420337709863059 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_185
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_185 : heightFactor (185 : Fin 988) ≤ ((658520529599781 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_185
  obtain ⟨hpl, hph⟩ := kernel_bounds_2026
  obtain ⟨hcl, hch⟩ := kernel_bounds_2027
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2027
  have h : (((4108729 / 2048 : ℚ) : ℝ) * (logKernel ((1013 / 32 : ℚ) : ℝ) - logKernel ((2027 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2027 / 64 : ℚ) : ℝ) + Real.log ((2027 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((658520529599781 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_186 : ((249025444776249089 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((507 / 16 : ℚ) : ℝ) ∧
    Real.log ((507 / 16 : ℚ) : ℝ) ≤ ((62256361194062273 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((249025444776249089 / 72057594037927936 : ℚ) : ℝ) ≤ ((507 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((507 / 16 : ℚ) : ℝ) ≤ Real.exp ((62256361194062273 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_186 : heightPower (186 : Fin 988) ≤ ((845212294835209 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_186
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_186 : heightFactor (186 : Fin 988) ≤ ((163111743981329 / 35184372088832 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_186
  obtain ⟨hpl, hph⟩ := kernel_bounds_2027
  obtain ⟨hcl, hch⟩ := kernel_bounds_2028
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2028
  have h : (((257049 / 128 : ℚ) : ℝ) * (logKernel ((2027 / 64 : ℚ) : ℝ) - logKernel ((507 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((507 / 16 : ℚ) : ℝ) + Real.log ((507 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((163111743981329 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_187 : ((124530483688468947 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2029 / 64 : ℚ) : ℝ) ∧
    Real.log ((2029 / 64 : ℚ) : ℝ) ≤ ((249060967376937897 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((124530483688468947 / 36028797018963968 : ℚ) : ℝ) ≤ ((2029 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2029 / 64 : ℚ) : ℝ) ≤ Real.exp ((249060967376937897 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_187 : heightPower (187 : Fin 988) ≤ ((849749101505253 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_187
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_187 : heightFactor (187 : Fin 988) ≤ ((646429072066973 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_187
  obtain ⟨hpl, hph⟩ := kernel_bounds_2028
  obtain ⟨hcl, hch⟩ := kernel_bounds_2029
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2029
  have h : (((4116841 / 2048 : ℚ) : ℝ) * (logKernel ((507 / 16 : ℚ) : ℝ) - logKernel ((2029 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2029 / 64 : ℚ) : ℝ) + Real.log ((2029 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((646429072066973 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_188 : ((124548236237248401 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((1015 / 32 : ℚ) : ℝ) ∧
    Real.log ((1015 / 32 : ℚ) : ℝ) ≤ ((249096472474496805 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((124548236237248401 / 36028797018963968 : ℚ) : ℝ) ≤ ((1015 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1015 / 32 : ℚ) : ℝ) ≤ Real.exp ((249096472474496805 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_188 : heightPower (188 : Fin 988) ≤ ((854285839803697 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_188
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_188 : heightFactor (188 : Fin 988) ≤ ((640466311888567 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_188
  obtain ⟨hpl, hph⟩ := kernel_bounds_2029
  obtain ⟨hcl, hch⟩ := kernel_bounds_2030
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2030
  have h : (((1030225 / 512 : ℚ) : ℝ) * (logKernel ((2029 / 64 : ℚ) : ℝ) - logKernel ((1015 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1015 / 32 : ℚ) : ℝ) + Real.log ((1015 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((640466311888567 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_189 : ((124565980043083015 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2031 / 64 : ℚ) : ℝ) ∧
    Real.log ((2031 / 64 : ℚ) : ℝ) ≤ ((249131960086166033 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((124565980043083015 / 36028797018963968 : ℚ) : ℝ) ≤ ((2031 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2031 / 64 : ℚ) : ℝ) ≤ Real.exp ((249131960086166033 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_189 : heightPower (189 : Fin 988) ≤ ((214705627449471 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_189
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_189 : heightFactor (189 : Fin 988) ≤ ((1269116387637187 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_189
  obtain ⟨hpl, hph⟩ := kernel_bounds_2030
  obtain ⟨hcl, hch⟩ := kernel_bounds_2031
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2031
  have h : (((4124961 / 2048 : ℚ) : ℝ) * (logKernel ((1015 / 32 : ℚ) : ℝ) - logKernel ((2031 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2031 / 64 : ℚ) : ℝ) + Real.log ((2031 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((1269116387637187 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_190 : ((249167430229160337 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((127 / 4 : ℚ) : ℝ) ∧
    Real.log ((127 / 4 : ℚ) : ℝ) ≤ ((62291857557290085 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((249167430229160337 / 72057594037927936 : ℚ) : ℝ) ≤ ((127 / 4 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((127 / 4 : ℚ) : ℝ) ≤ Real.exp ((62291857557290085 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_190 : heightPower (190 : Fin 988) ≤ ((863359111555059 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_190
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_190 : heightFactor (190 : Fin 988) ≤ ((628704220809457 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_190
  obtain ⟨hpl, hph⟩ := kernel_bounds_2031
  obtain ⟨hcl, hch⟩ := kernel_bounds_2032
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2032
  have h : (((16129 / 8 : ℚ) : ℝ) * (logKernel ((2031 / 64 : ℚ) : ℝ) - logKernel ((127 / 4 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((127 / 4 : ℚ) : ℝ) + Real.log ((127 / 4 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((628704220809457 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_191 : ((249202882920669071 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2033 / 64 : ℚ) : ℝ) ∧
    Real.log ((2033 / 64 : ℚ) : ℝ) ≤ ((124601441460334537 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((249202882920669071 / 72057594037927936 : ℚ) : ℝ) ≤ ((2033 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2033 / 64 : ℚ) : ℝ) ≤ Real.exp ((124601441460334537 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_191 : heightPower (191 : Fin 988) ≤ ((867895645142369 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_191
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_191 : heightFactor (191 : Fin 988) ≤ ((622903900297061 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_191
  obtain ⟨hpl, hph⟩ := kernel_bounds_2032
  obtain ⟨hcl, hch⟩ := kernel_bounds_2033
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2033
  have h : (((4133089 / 2048 : ℚ) : ℝ) * (logKernel ((127 / 4 : ℚ) : ℝ) - logKernel ((2033 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2033 / 64 : ℚ) : ℝ) + Real.log ((2033 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((622903900297061 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

end LegendreK6.M2Pilot.Enclosures.Height005
