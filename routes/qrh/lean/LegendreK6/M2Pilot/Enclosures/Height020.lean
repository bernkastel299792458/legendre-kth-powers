import LegendreK6.M2PilotDefinitions
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp

/-! Generated proposals: every bound is checked by Lean, not by trusting Arb. -/
namespace LegendreK6.M2Pilot.Enclosures.Height020
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem height_z_bounds_2481 : ((50749702829787 / 2305843009213693952 : ℚ) : ℝ) ≤ heightZ ((2481 / 64 : ℚ) : ℝ) ∧
    heightZ ((2481 / 64 : ℚ) : ℝ) ≤ ((405997622638299 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((50749702829787 / 2305843009213693952 : ℚ) : ℝ) ≤ Real.exp (-((2481 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1715 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2481 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1715 / 192 : ℚ) : ℝ) ≤ ((405997622638299 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2481 : ((4611960161 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2481 / 64 : ℚ) : ℝ) ∧
    logKernel ((2481 / 64 : ℚ) : ℝ) ≤ ((2305980083 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2481
  constructor
  · exact (show ((4611960161 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((50749702829787 / 2305843009213693952 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2481 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((405997622638299 / 18446744073709551616 : ℚ) : ℝ) ≤ ((2305980083 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2482 : ((399703212920069 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1241 / 32 : ℚ) : ℝ) ∧
    heightZ ((1241 / 32 : ℚ) : ℝ) ≤ ((49962901615009 / 2305843009213693952 : ℚ) : ℝ) := by
  have h : ((399703212920069 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1241 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-859 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1241 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-859 / 96 : ℚ) : ℝ) ≤ ((49962901615009 / 2305843009213693952 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2482 : ((558758133 / 9007199254740992 : ℚ) : ℝ) ≤ logKernel ((1241 / 32 : ℚ) : ℝ) ∧
    logKernel ((1241 / 32 : ℚ) : ℝ) ≤ ((4470065069 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2482
  constructor
  · exact (show ((558758133 / 9007199254740992 : ℚ) : ℝ) ≤ zKernel ((399703212920069 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1241 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((49962901615009 / 2305843009213693952 : ℚ) : ℝ) ≤ ((4470065069 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2483 : ((196753194489711 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2483 / 64 : ℚ) : ℝ) ∧
    heightZ ((2483 / 64 : ℚ) : ℝ) ≤ ((393506388979425 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((196753194489711 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2483 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1721 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2483 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1721 / 192 : ℚ) : ℝ) ≤ ((393506388979425 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2483 : ((4332535621 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2483 / 64 : ℚ) : ℝ) ∧
    logKernel ((2483 / 64 : ℚ) : ℝ) ≤ ((2166267813 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2483
  constructor
  · exact (show ((4332535621 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((196753194489711 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2483 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((393506388979425 / 18446744073709551616 : ℚ) : ℝ) ≤ ((2166267813 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2484 : ((387405637889105 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((621 / 16 : ℚ) : ℝ) ∧
    heightZ ((621 / 16 : ℚ) : ℝ) ≤ ((96851409472277 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((387405637889105 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((621 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-431 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((621 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-431 / 48 : ℚ) : ℝ) ≤ ((96851409472277 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2484 : ((4199237513 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((621 / 16 : ℚ) : ℝ) ∧
    logKernel ((621 / 16 : ℚ) : ℝ) ≤ ((2099618759 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2484
  constructor
  · exact (show ((4199237513 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((387405637889105 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((621 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((96851409472277 / 4611686018427387904 : ℚ) : ℝ) ≤ ((2099618759 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2485 : ((381399470177631 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2485 / 64 : ℚ) : ℝ) ∧
    heightZ ((2485 / 64 : ℚ) : ℝ) ≤ ((190699735088817 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((381399470177631 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2485 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1727 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2485 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1727 / 192 : ℚ) : ℝ) ≤ ((190699735088817 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2485 : ((4070040557 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2485 / 64 : ℚ) : ℝ) ∧
    logKernel ((2485 / 64 : ℚ) : ℝ) ≤ ((2035020281 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2485
  constructor
  · exact (show ((4070040557 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((381399470177631 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2485 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((190699735088817 / 9223372036854775808 : ℚ) : ℝ) ≤ ((2035020281 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2486 : ((375486419465629 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1243 / 32 : ℚ) : ℝ) ∧
    heightZ ((1243 / 32 : ℚ) : ℝ) ≤ ((11733950608301 / 576460752303423488 : ℚ) : ℝ) := by
  have h : ((375486419465629 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1243 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-865 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1243 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-865 / 96 : ℚ) : ℝ) ≤ ((11733950608301 / 576460752303423488 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2486 : ((3944818573 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1243 / 32 : ℚ) : ℝ) ∧
    logKernel ((1243 / 32 : ℚ) : ℝ) ≤ ((1972409289 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2486
  constructor
  · exact (show ((3944818573 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((375486419465629 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1243 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((11733950608301 / 576460752303423488 : ℚ) : ℝ) ≤ ((1972409289 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2487 : ((184832521053915 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2487 / 64 : ℚ) : ℝ) ∧
    heightZ ((2487 / 64 : ℚ) : ℝ) ≤ ((369665042107833 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((184832521053915 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2487 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1733 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2487 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1733 / 192 : ℚ) : ℝ) ≤ ((369665042107833 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2487 : ((3823449265 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2487 / 64 : ℚ) : ℝ) ∧
    logKernel ((2487 / 64 : ℚ) : ℝ) ≤ ((1911724635 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2487
  constructor
  · exact (show ((3823449265 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((184832521053915 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2487 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((369665042107833 / 18446744073709551616 : ℚ) : ℝ) ≤ ((1911724635 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2488 : ((90983479210153 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((311 / 8 : ℚ) : ℝ) ∧
    heightZ ((311 / 8 : ℚ) : ℝ) ≤ ((363933916840615 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((90983479210153 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((311 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-217 / 24 : ℚ) : ℝ) ∧
      Real.exp (-((311 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-217 / 24 : ℚ) : ℝ) ≤ ((363933916840615 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2488 : ((1852907049 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((311 / 8 : ℚ) : ℝ) ∧
    logKernel ((311 / 8 : ℚ) : ℝ) ≤ ((3705814103 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2488
  constructor
  · exact (show ((1852907049 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((90983479210153 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((311 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((363933916840615 / 18446744073709551616 : ℚ) : ℝ) ≤ ((3705814103 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2489 : ((179145822217503 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2489 / 64 : ℚ) : ℝ) ∧
    heightZ ((2489 / 64 : ℚ) : ℝ) ≤ ((358291644435009 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((179145822217503 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2489 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1739 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2489 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1739 / 192 : ℚ) : ℝ) ≤ ((358291644435009 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2489 : ((3591798185 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2489 / 64 : ℚ) : ℝ) ∧
    logKernel ((2489 / 64 : ℚ) : ℝ) ≤ ((1795899095 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2489
  constructor
  · exact (show ((3591798185 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((179145822217503 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2489 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((358291644435009 / 18446744073709551616 : ℚ) : ℝ) ≤ ((1795899095 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2490 : ((5511513239923 / 288230376151711744 : ℚ) : ℝ) ≤ heightZ ((1245 / 32 : ℚ) : ℝ) ∧
    heightZ ((1245 / 32 : ℚ) : ℝ) ≤ ((352736847355075 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((5511513239923 / 288230376151711744 : ℚ) : ℝ) ≤ Real.exp (-((1245 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-871 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1245 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-871 / 96 : ℚ) : ℝ) ≤ ((352736847355075 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2490 : ((870322543 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((1245 / 32 : ℚ) : ℝ) ∧
    logKernel ((1245 / 32 : ℚ) : ℝ) ≤ ((3481290177 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2490
  constructor
  · exact (show ((870322543 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((5511513239923 / 288230376151711744 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1245 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((352736847355075 / 18446744073709551616 : ℚ) : ℝ) ≤ ((3481290177 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2491 : ((347268169421589 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2491 / 64 : ℚ) : ℝ) ∧
    heightZ ((2491 / 64 : ℚ) : ℝ) ≤ ((43408521177699 / 2305843009213693952 : ℚ) : ℝ) := by
  have h : ((347268169421589 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2491 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1745 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2491 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1745 / 192 : ℚ) : ℝ) ≤ ((43408521177699 / 2305843009213693952 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2491 : ((3374182133 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2491 / 64 : ℚ) : ℝ) ∧
    logKernel ((2491 / 64 : ℚ) : ℝ) ≤ ((1687091069 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2491
  constructor
  · exact (show ((3374182133 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((347268169421589 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2491 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((43408521177699 / 2305843009213693952 : ℚ) : ℝ) ≤ ((1687091069 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2492 : ((21367767217559 / 1152921504606846976 : ℚ) : ℝ) ≤ heightZ ((623 / 16 : ℚ) : ℝ) ∧
    heightZ ((623 / 16 : ℚ) : ℝ) ≤ ((341884275480947 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((21367767217559 / 1152921504606846976 : ℚ) : ℝ) ≤ Real.exp (-((623 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-437 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((623 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-437 / 48 : ℚ) : ℝ) ≤ ((341884275480947 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2492 : ((3270369463 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((623 / 16 : ℚ) : ℝ) ∧
    logKernel ((623 / 16 : ℚ) : ℝ) ≤ ((817592367 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2492
  constructor
  · exact (show ((3270369463 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((21367767217559 / 1152921504606846976 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((623 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((341884275480947 / 18446744073709551616 : ℚ) : ℝ) ≤ ((817592367 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2493 : ((336583851079165 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2493 / 64 : ℚ) : ℝ) ∧
    heightZ ((2493 / 64 : ℚ) : ℝ) ≤ ((657390334139 / 36028797018963968 : ℚ) : ℝ) := by
  have h : ((336583851079165 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2493 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1751 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2493 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1751 / 192 : ℚ) : ℝ) ≤ ((657390334139 / 36028797018963968 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2493 : ((792437693 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((2493 / 64 : ℚ) : ℝ) ∧
    logKernel ((2493 / 64 : ℚ) : ℝ) ≤ ((3169750777 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2493
  constructor
  · exact (show ((792437693 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((336583851079165 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2493 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((657390334139 / 36028797018963968 : ℚ) : ℝ) ≤ ((3169750777 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2494 : ((331365602140997 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1247 / 32 : ℚ) : ℝ) ∧
    heightZ ((1247 / 32 : ℚ) : ℝ) ≤ ((41420700267625 / 2305843009213693952 : ℚ) : ℝ) := by
  have h : ((331365602140997 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1247 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-877 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1247 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-877 / 96 : ℚ) : ℝ) ≤ ((41420700267625 / 2305843009213693952 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2494 : ((3072227793 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1247 / 32 : ℚ) : ℝ) ∧
    logKernel ((1247 / 32 : ℚ) : ℝ) ≤ ((1536113899 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2494
  constructor
  · exact (show ((3072227793 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((331365602140997 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1247 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((41420700267625 / 2305843009213693952 : ℚ) : ℝ) ≤ ((1536113899 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2495 : ((326228254653963 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2495 / 64 : ℚ) : ℝ) ∧
    heightZ ((2495 / 64 : ℚ) : ℝ) ≤ ((163114127326983 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((326228254653963 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2495 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1757 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2495 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1757 / 192 : ℚ) : ℝ) ≤ ((163114127326983 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2495 : ((2977705281 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2495 / 64 : ℚ) : ℝ) ∧
    logKernel ((2495 / 64 : ℚ) : ℝ) ≤ ((1488852643 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2495
  constructor
  · exact (show ((2977705281 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((326228254653963 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2495 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((163114127326983 / 9223372036854775808 : ℚ) : ℝ) ≤ ((1488852643 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2496 : ((40146319294665 / 2305843009213693952 : ℚ) : ℝ) ≤ heightZ ((39 / 1 : ℚ) : ℝ) ∧
    heightZ ((39 / 1 : ℚ) : ℝ) ≤ ((321170554357323 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((40146319294665 / 2305843009213693952 : ℚ) : ℝ) ≤ Real.exp (-((39 / 1 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-55 / 6 : ℚ) : ℝ) ∧
      Real.exp (-((39 / 1 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-55 / 6 : ℚ) : ℝ) ≤ ((321170554357323 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2496 : ((2886090921 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((39 / 1 : ℚ) : ℝ) ∧
    logKernel ((39 / 1 : ℚ) : ℝ) ≤ ((1443045463 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2496
  constructor
  · exact (show ((2886090921 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((40146319294665 / 2305843009213693952 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((39 / 1 : ℚ) : ℝ)) hh).trans
      (show zKernel ((321170554357323 / 18446744073709551616 : ℚ) : ℝ) ≤ ((1443045463 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2497 : ((316191266435833 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2497 / 64 : ℚ) : ℝ) ∧
    heightZ ((2497 / 64 : ℚ) : ℝ) ≤ ((79047816608959 / 4611686018427387904 : ℚ) : ℝ) := by
  have h : ((316191266435833 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2497 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1763 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2497 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1763 / 192 : ℚ) : ℝ) ≤ ((79047816608959 / 4611686018427387904 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2497 : ((1398647619 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2497 / 64 : ℚ) : ℝ) ∧
    logKernel ((2497 / 64 : ℚ) : ℝ) ≤ ((2797295243 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2497
  constructor
  · exact (show ((1398647619 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((316191266435833 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2497 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((79047816608959 / 4611686018427387904 : ℚ) : ℝ) ≤ ((2797295243 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2498 : ((155644587609153 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((1249 / 32 : ℚ) : ℝ) ∧
    heightZ ((1249 / 32 : ℚ) : ℝ) ≤ ((311289175218309 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((155644587609153 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((1249 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-883 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1249 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-883 / 96 : ℚ) : ℝ) ≤ ((311289175218309 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2498 : ((2711231511 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1249 / 32 : ℚ) : ℝ) ∧
    logKernel ((1249 / 32 : ℚ) : ℝ) ≤ ((677807879 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2498
  constructor
  · exact (show ((2711231511 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((155644587609153 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1249 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((311289175218309 / 18446744073709551616 : ℚ) : ℝ) ≤ ((677807879 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2499 : ((153231541940387 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2499 / 64 : ℚ) : ℝ) ∧
    heightZ ((2499 / 64 : ℚ) : ℝ) ≤ ((306463083880777 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((153231541940387 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2499 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1769 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2499 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1769 / 192 : ℚ) : ℝ) ≤ ((306463083880777 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2499 : ((2627815687 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2499 / 64 : ℚ) : ℝ) ∧
    logKernel ((2499 / 64 : ℚ) : ℝ) ≤ ((656953923 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2499
  constructor
  · exact (show ((2627815687 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((153231541940387 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2499 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((306463083880777 / 18446744073709551616 : ℚ) : ℝ) ≤ ((656953923 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2500 : ((37713976769289 / 2305843009213693952 : ℚ) : ℝ) ≤ heightZ ((625 / 16 : ℚ) : ℝ) ∧
    heightZ ((625 / 16 : ℚ) : ℝ) ≤ ((301711814154315 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((37713976769289 / 2305843009213693952 : ℚ) : ℝ) ≤ Real.exp (-((625 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-443 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((625 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-443 / 48 : ℚ) : ℝ) ≤ ((301711814154315 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2500 : ((1273483149 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((625 / 16 : ℚ) : ℝ) ∧
    logKernel ((625 / 16 : ℚ) : ℝ) ≤ ((2546966303 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2500
  constructor
  · exact (show ((1273483149 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((37713976769289 / 2305843009213693952 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((625 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((301711814154315 / 18446744073709551616 : ℚ) : ℝ) ≤ ((2546966303 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2501 : ((148517103018679 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2501 / 64 : ℚ) : ℝ) ∧
    heightZ ((2501 / 64 : ℚ) : ℝ) ≤ ((297034206037361 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((148517103018679 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2501 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1775 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2501 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1775 / 192 : ℚ) : ℝ) ≤ ((297034206037361 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2501 : ((2468604383 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2501 / 64 : ℚ) : ℝ) ∧
    logKernel ((2501 / 64 : ℚ) : ℝ) ≤ ((617151097 / 18014398509481984 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2501
  constructor
  · exact (show ((2468604383 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((148517103018679 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2501 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((297034206037361 / 18446744073709551616 : ℚ) : ℝ) ≤ ((617151097 / 18014398509481984 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2502 : ((292429117512509 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((1251 / 32 : ℚ) : ℝ) ∧
    heightZ ((1251 / 32 : ℚ) : ℝ) ≤ ((4569204961133 / 288230376151711744 : ℚ) : ℝ) := by
  have h : ((292429117512509 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((1251 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-889 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1251 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-889 / 96 : ℚ) : ℝ) ≤ ((4569204961133 / 288230376151711744 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2502 : ((2392653411 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1251 / 32 : ℚ) : ℝ) ∧
    logKernel ((1251 / 32 : ℚ) : ℝ) ≤ ((299081677 / 9007199254740992 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2502
  constructor
  · exact (show ((2392653411 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((292429117512509 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1251 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((4569204961133 / 288230376151711744 : ℚ) : ℝ) ≤ ((299081677 / 9007199254740992 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2503 : ((287895424267701 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2503 / 64 : ℚ) : ℝ) ∧
    heightZ ((2503 / 64 : ℚ) : ℝ) ≤ ((35986928033463 / 2305843009213693952 : ℚ) : ℝ) := by
  have h : ((287895424267701 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2503 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1781 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2503 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1781 / 192 : ℚ) : ℝ) ≤ ((35986928033463 / 2305843009213693952 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2503 : ((579759801 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((2503 / 64 : ℚ) : ℝ) ∧
    logKernel ((2503 / 64 : ℚ) : ℝ) ≤ ((2319039209 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2503
  constructor
  · exact (show ((579759801 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((287895424267701 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2503 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((35986928033463 / 2305843009213693952 : ℚ) : ℝ) ≤ ((2319039209 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2504 : ((17714501213857 / 1152921504606846976 : ℚ) : ℝ) ≤ heightZ ((313 / 8 : ℚ) : ℝ) ∧
    heightZ ((313 / 8 : ℚ) : ℝ) ≤ ((283432019421715 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((17714501213857 / 1152921504606846976 : ℚ) : ℝ) ≤ Real.exp (-((313 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-223 / 24 : ℚ) : ℝ) ∧
      Real.exp (-((313 / 8 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-223 / 24 : ℚ) : ℝ) ≤ ((283432019421715 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2504 : ((2247689869 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((313 / 8 : ℚ) : ℝ) ∧
    logKernel ((313 / 8 : ℚ) : ℝ) ≤ ((1123844937 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2504
  constructor
  · exact (show ((2247689869 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((17714501213857 / 1152921504606846976 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((313 / 8 : ℚ) : ℝ)) hh).trans
      (show zKernel ((283432019421715 / 18446744073709551616 : ℚ) : ℝ) ≤ ((1123844937 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2505 : ((279037813253923 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2505 / 64 : ℚ) : ℝ) ∧
    heightZ ((2505 / 64 : ℚ) : ℝ) ≤ ((139518906626963 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((279037813253923 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2505 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1787 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2505 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1787 / 192 : ℚ) : ℝ) ≤ ((139518906626963 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2505 : ((2178535721 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2505 / 64 : ℚ) : ℝ) ∧
    logKernel ((2505 / 64 : ℚ) : ℝ) ≤ ((1089267863 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2505
  constructor
  · exact (show ((2178535721 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((279037813253923 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2505 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((139518906626963 / 9223372036854775808 : ℚ) : ℝ) ≤ ((1089267863 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2506 : ((68677933234567 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((1253 / 32 : ℚ) : ℝ) ∧
    heightZ ((1253 / 32 : ℚ) : ℝ) ≤ ((274711732938271 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((68677933234567 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((1253 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-895 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1253 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-895 / 96 : ℚ) : ℝ) ≤ ((274711732938271 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2506 : ((263938653 / 9007199254740992 : ℚ) : ℝ) ≤ logKernel ((1253 / 32 : ℚ) : ℝ) ∧
    logKernel ((1253 / 32 : ℚ) : ℝ) ≤ ((2111509229 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2506
  constructor
  · exact (show ((263938653 / 9007199254740992 : ℚ) : ℝ) ≤ zKernel ((68677933234567 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1253 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((274711732938271 / 18446744073709551616 : ℚ) : ℝ) ≤ ((2111509229 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2507 : ((135226361140653 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2507 / 64 : ℚ) : ℝ) ∧
    heightZ ((2507 / 64 : ℚ) : ℝ) ≤ ((270452722281309 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((135226361140653 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2507 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1793 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2507 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1793 / 192 : ℚ) : ℝ) ≤ ((270452722281309 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2507 : ((1023272457 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2507 / 64 : ℚ) : ℝ) ∧
    logKernel ((2507 / 64 : ℚ) : ℝ) ≤ ((2046544919 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2507
  constructor
  · exact (show ((1023272457 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((135226361140653 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2507 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((270452722281309 / 18446744073709551616 : ℚ) : ℝ) ≤ ((2046544919 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2508 : ((266259741464359 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((627 / 16 : ℚ) : ℝ) ∧
    heightZ ((627 / 16 : ℚ) : ℝ) ≤ ((133129870732181 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((266259741464359 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((627 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-449 / 48 : ℚ) : ℝ) ∧
      Real.exp (-((627 / 16 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-449 / 48 : ℚ) : ℝ) ≤ ((133129870732181 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2508 : ((1983579347 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((627 / 16 : ℚ) : ℝ) ∧
    logKernel ((627 / 16 : ℚ) : ℝ) ≤ ((247947419 / 9007199254740992 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2508
  constructor
  · exact (show ((1983579347 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((266259741464359 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((627 / 16 : ℚ) : ℝ)) hh).trans
      (show zKernel ((133129870732181 / 9223372036854775808 : ℚ) : ℝ) ≤ ((247947419 / 9007199254740992 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2509 : ((262131766789643 / 18446744073709551616 : ℚ) : ℝ) ≤ heightZ ((2509 / 64 : ℚ) : ℝ) ∧
    heightZ ((2509 / 64 : ℚ) : ℝ) ≤ ((131065883394823 / 9223372036854775808 : ℚ) : ℝ) := by
  have h : ((262131766789643 / 18446744073709551616 : ℚ) : ℝ) ≤ Real.exp (-((2509 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1799 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2509 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1799 / 192 : ℚ) : ℝ) ≤ ((131065883394823 / 9223372036854775808 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2509 : ((961275513 / 36028797018963968 : ℚ) : ℝ) ≤ logKernel ((2509 / 64 : ℚ) : ℝ) ∧
    logKernel ((2509 / 64 : ℚ) : ℝ) ≤ ((1922551031 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2509
  constructor
  · exact (show ((961275513 / 36028797018963968 : ℚ) : ℝ) ≤ zKernel ((262131766789643 / 18446744073709551616 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2509 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((131065883394823 / 9223372036854775808 : ℚ) : ℝ) ≤ ((1922551031 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2510 : ((2016154612737 / 144115188075855872 : ℚ) : ℝ) ≤ heightZ ((1255 / 32 : ℚ) : ℝ) ∧
    heightZ ((1255 / 32 : ℚ) : ℝ) ≤ ((258067790430339 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((2016154612737 / 144115188075855872 : ℚ) : ℝ) ≤ Real.exp (-((1255 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-901 / 96 : ℚ) : ℝ) ∧
      Real.exp (-((1255 / 32 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-901 / 96 : ℚ) : ℝ) ≤ ((258067790430339 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2510 : ((1863400349 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((1255 / 32 : ℚ) : ℝ) ∧
    logKernel ((1255 / 32 : ℚ) : ℝ) ≤ ((931700177 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2510
  constructor
  · exact (show ((1863400349 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((2016154612737 / 144115188075855872 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((1255 / 32 : ℚ) : ℝ)) hh).trans
      (show zKernel ((258067790430339 / 18446744073709551616 : ℚ) : ℝ) ≤ ((931700177 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2511 : ((63516705046131 / 4611686018427387904 : ℚ) : ℝ) ≤ heightZ ((2511 / 64 : ℚ) : ℝ) ∧
    heightZ ((2511 / 64 : ℚ) : ℝ) ≤ ((254066820184527 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((63516705046131 / 4611686018427387904 : ℚ) : ℝ) ≤ Real.exp (-((2511 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1805 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2511 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1805 / 192 : ℚ) : ℝ) ≤ ((254066820184527 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2511 : ((451517387 / 18014398509481984 : ℚ) : ℝ) ≤ logKernel ((2511 / 64 : ℚ) : ℝ) ∧
    logKernel ((2511 / 64 : ℚ) : ℝ) ≤ ((1806069553 / 72057594037927936 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2511
  constructor
  · exact (show ((451517387 / 18014398509481984 : ℚ) : ℝ) ≤ zKernel ((63516705046131 / 4611686018427387904 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2511 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((254066820184527 / 18446744073709551616 : ℚ) : ℝ) ≤ ((1806069553 / 72057594037927936 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2512 : ((125063939616479 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((157 / 4 : ℚ) : ℝ) ∧
    heightZ ((157 / 4 : ℚ) : ℝ) ≤ ((250127879232961 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((125063939616479 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((157 / 4 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-113 / 12 : ℚ) : ℝ) ∧
      Real.exp (-((157 / 4 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-113 / 12 : ℚ) : ℝ) ≤ ((250127879232961 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2512 : ((1750502629 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((157 / 4 : ℚ) : ℝ) ∧
    logKernel ((157 / 4 : ℚ) : ℝ) ≤ ((875251317 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2512
  constructor
  · exact (show ((1750502629 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((125063939616479 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((157 / 4 : ℚ) : ℝ)) hh).trans
      (show zKernel ((250127879232961 / 18446744073709551616 : ℚ) : ℝ) ≤ ((875251317 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem height_z_bounds_2513 : ((123125002950283 / 9223372036854775808 : ℚ) : ℝ) ≤ heightZ ((2513 / 64 : ℚ) : ℝ) ∧
    heightZ ((2513 / 64 : ℚ) : ℝ) ≤ ((246250005900569 / 18446744073709551616 : ℚ) : ℝ) := by
  have h : ((123125002950283 / 9223372036854775808 : ℚ) : ℝ) ≤ Real.exp (-((2513 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1811 / 192 : ℚ) : ℝ) ∧
      Real.exp (-((2513 / 64 : ℚ) : ℝ)) + ((1 / 6 : ℚ) : ℝ) * Real.exp ((-1811 / 192 : ℚ) : ℝ) ≤ ((246250005900569 / 18446744073709551616 : ℚ) : ℝ) := by
    constructor <;> dyadic_interval [prec := 80]
  norm_num [heightZ, right] at h ⊢
  constructor <;> linarith
theorem kernel_bounds_2513 : ((1696645325 / 72057594037927936 : ℚ) : ℝ) ≤ logKernel ((2513 / 64 : ℚ) : ℝ) ∧
    logKernel ((2513 / 64 : ℚ) : ℝ) ≤ ((848322665 / 36028797018963968 : ℚ) : ℝ) := by
  obtain ⟨hl, hh⟩ := height_z_bounds_2513
  constructor
  · exact (show ((1696645325 / 72057594037927936 : ℚ) : ℝ) ≤ zKernel ((123125002950283 / 9223372036854775808 : ℚ) : ℝ) by norm_num [zKernel]).trans
      (zKernel_monotone (by norm_num) hl)
  · exact (zKernel_monotone (heightZ_nonneg ((2513 / 64 : ℚ) : ℝ)) hh).trans
      (show zKernel ((246250005900569 / 18446744073709551616 : ℚ) : ℝ) ≤ ((848322665 / 36028797018963968 : ℚ) : ℝ) by norm_num [zKernel])

theorem log_height_bounds_640 : ((263582130888694629 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1241 / 32 : ℚ) : ℝ) ∧
    Real.log ((1241 / 32 : ℚ) : ℝ) ≤ ((32947766361086829 / 9007199254740992 : ℚ) : ℝ) := by
  have hl : Real.exp ((263582130888694629 / 72057594037927936 : ℚ) : ℝ) ≤ ((1241 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1241 / 32 : ℚ) : ℝ) ≤ Real.exp ((32947766361086829 / 9007199254740992 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_640 : heightPower (640 : Fin 988) ≤ ((2898787466003165 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_640
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_640 : heightFactor (640 : Fin 988) ≤ ((51626312927 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_640
  obtain ⟨hpl, hph⟩ := kernel_bounds_2481
  obtain ⟨hcl, hch⟩ := kernel_bounds_2482
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2482
  have h : (((1540081 / 512 : ℚ) : ℝ) * (logKernel ((2481 / 64 : ℚ) : ℝ) - logKernel ((1241 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1241 / 32 : ℚ) : ℝ) + Real.log ((1241 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((51626312927 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_641 : ((263611157110250435 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2483 / 64 : ℚ) : ℝ) ∧
    Real.log ((2483 / 64 : ℚ) : ℝ) ≤ ((131805578555125219 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((263611157110250435 / 72057594037927936 : ℚ) : ℝ) ≤ ((2483 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2483 / 64 : ℚ) : ℝ) ≤ Real.exp ((131805578555125219 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_641 : heightPower (641 : Fin 988) ≤ ((2903298896192221 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_641
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_641 : heightFactor (641 : Fin 988) ≤ ((25173266563 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_641
  obtain ⟨hpl, hph⟩ := kernel_bounds_2482
  obtain ⟨hcl, hch⟩ := kernel_bounds_2483
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2483
  have h : (((6165289 / 2048 : ℚ) : ℝ) * (logKernel ((1241 / 32 : ℚ) : ℝ) - logKernel ((2483 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2483 / 64 : ℚ) : ℝ) + Real.log ((2483 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((25173266563 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_642 : ((263640171644178965 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((621 / 16 : ℚ) : ℝ) ∧
    Real.log ((621 / 16 : ℚ) : ℝ) ≤ ((32955021455522371 / 9007199254740992 : ℚ) : ℝ) := by
  have hl : Real.exp ((263640171644178965 / 72057594037927936 : ℚ) : ℝ) ≤ ((621 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((621 / 16 : ℚ) : ℝ) ≤ Real.exp ((32955021455522371 / 9007199254740992 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_642 : heightPower (642 : Fin 988) ≤ ((726952570181621 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_642
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_642 : heightFactor (642 : Fin 988) ≤ ((49098459619 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_642
  obtain ⟨hpl, hph⟩ := kernel_bounds_2483
  obtain ⟨hcl, hch⟩ := kernel_bounds_2484
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2484
  have h : (((385641 / 128 : ℚ) : ℝ) * (logKernel ((2483 / 64 : ℚ) : ℝ) - logKernel ((621 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((621 / 16 : ℚ) : ℝ) + Real.log ((621 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((49098459619 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_643 : ((131834587249944327 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2485 / 64 : ℚ) : ℝ) ∧
    Real.log ((2485 / 64 : ℚ) : ℝ) ≤ ((263669174499888657 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((131834587249944327 / 36028797018963968 : ℚ) : ℝ) ≤ ((2485 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2485 / 64 : ℚ) : ℝ) ≤ Real.exp ((263669174499888657 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_643 : heightPower (643 : Fin 988) ≤ ((182020101227669 / 17592186044416 : ℚ) : ℝ) := by
  have hh := log_height_bounds_643
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_643 : heightFactor (643 : Fin 988) ≤ ((23940653683 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_643
  obtain ⟨hpl, hph⟩ := kernel_bounds_2484
  obtain ⟨hcl, hch⟩ := kernel_bounds_2485
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2485
  have h : (((6175225 / 2048 : ℚ) : ℝ) * (logKernel ((621 / 16 : ℚ) : ℝ) - logKernel ((2485 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2485 / 64 : ℚ) : ℝ) + Real.log ((2485 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((23940653683 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_644 : ((263698165686776579 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1243 / 32 : ℚ) : ℝ) ∧
    Real.log ((1243 / 32 : ℚ) : ℝ) ≤ ((131849082843388291 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((263698165686776579 / 72057594037927936 : ℚ) : ℝ) ≤ ((1243 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1243 / 32 : ℚ) : ℝ) ≤ Real.exp ((131849082843388291 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_644 : heightPower (644 : Fin 988) ≤ ((2916832912977589 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_644
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_644 : heightFactor (644 : Fin 988) ≤ ((46694310749 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_644
  obtain ⟨hpl, hph⟩ := kernel_bounds_2485
  obtain ⟨hcl, hch⟩ := kernel_bounds_2486
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2486
  have h : (((1545049 / 512 : ℚ) : ℝ) * (logKernel ((2485 / 64 : ℚ) : ℝ) - logKernel ((1243 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1243 / 32 : ℚ) : ℝ) + Real.log ((1243 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((46694310749 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_645 : ((131863572607114241 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2487 / 64 : ℚ) : ℝ) ∧
    Real.log ((2487 / 64 : ℚ) : ℝ) ≤ ((263727145214228485 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((131863572607114241 / 36028797018963968 : ℚ) : ℝ) ≤ ((2487 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2487 / 64 : ℚ) : ℝ) ≤ Real.exp ((263727145214228485 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_645 : heightPower (645 : Fin 988) ≤ ((1460672080383901 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_645
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_645 : heightFactor (645 : Fin 988) ≤ ((22768361549 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_645
  obtain ⟨hpl, hph⟩ := kernel_bounds_2486
  obtain ⟨hcl, hch⟩ := kernel_bounds_2487
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2487
  have h : (((6185169 / 2048 : ℚ) : ℝ) * (logKernel ((1243 / 32 : ℚ) : ℝ) - logKernel ((2487 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2487 / 64 : ℚ) : ℝ) + Real.log ((2487 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((22768361549 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_646 : ((8242378534113087 / 2251799813685248 : ℚ) : ℝ) ≤ Real.log ((311 / 8 : ℚ) : ℝ) ∧
    Real.log ((311 / 8 : ℚ) : ℝ) ≤ ((263756113091618787 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((8242378534113087 / 2251799813685248 : ℚ) : ℝ) ≤ ((311 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((311 / 8 : ℚ) : ℝ) ≤ Real.exp ((263756113091618787 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_646 : heightPower (646 : Fin 988) ≤ ((2925855363049961 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_646
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_646 : heightFactor (646 : Fin 988) ≤ ((44407816217 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_646
  obtain ⟨hpl, hph⟩ := kernel_bounds_2487
  obtain ⟨hcl, hch⟩ := kernel_bounds_2488
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2488
  have h : (((96721 / 32 : ℚ) : ℝ) * (logKernel ((2487 / 64 : ℚ) : ℝ) - logKernel ((311 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((311 / 8 : ℚ) : ℝ) + Real.log ((311 / 8 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((44407816217 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_647 : ((263785069328310605 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2489 / 64 : ℚ) : ℝ) ∧
    Real.log ((2489 / 64 : ℚ) : ℝ) ≤ ((16486566833019413 / 4503599627370496 : ℚ) : ℝ) := by
  have hl : Real.exp ((263785069328310605 / 72057594037927936 : ℚ) : ℝ) ≤ ((2489 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2489 / 64 : ℚ) : ℝ) ≤ Real.exp ((16486566833019413 / 4503599627370496 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_647 : heightPower (647 : Fin 988) ≤ ((2930366519860643 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_647
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_647 : heightFactor (647 : Fin 988) ≤ ((21653439965 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_647
  obtain ⟨hpl, hph⟩ := kernel_bounds_2488
  obtain ⟨hcl, hch⟩ := kernel_bounds_2489
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2489
  have h : (((6195121 / 2048 : ℚ) : ℝ) * (logKernel ((311 / 8 : ℚ) : ℝ) - logKernel ((2489 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2489 / 64 : ℚ) : ℝ) + Real.log ((2489 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((21653439965 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_648 : ((131907006966827891 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((1245 / 32 : ℚ) : ℝ) ∧
    Real.log ((1245 / 32 : ℚ) : ℝ) ≤ ((263814013933655785 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((131907006966827891 / 36028797018963968 : ℚ) : ℝ) ≤ ((1245 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1245 / 32 : ℚ) : ℝ) ≤ Real.exp ((263814013933655785 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_648 : heightPower (648 : Fin 988) ≤ ((366859703904547 / 35184372088832 : ℚ) : ℝ) := by
  have hh := log_height_bounds_648
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_648 : heightFactor (648 : Fin 988) ≤ ((42233221637 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_648
  obtain ⟨hpl, hph⟩ := kernel_bounds_2489
  obtain ⟨hcl, hch⟩ := kernel_bounds_2490
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2490
  have h : (((1550025 / 512 : ℚ) : ℝ) * (logKernel ((2489 / 64 : ℚ) : ℝ) - logKernel ((1245 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1245 / 32 : ℚ) : ℝ) + Real.log ((1245 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((42233221637 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_649 : ((131921473458497443 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2491 / 64 : ℚ) : ℝ) ∧
    Real.log ((2491 / 64 : ℚ) : ℝ) ≤ ((263842946916994889 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((131921473458497443 / 36028797018963968 : ℚ) : ℝ) ≤ ((2491 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2491 / 64 : ℚ) : ℝ) ≤ Real.exp ((263842946916994889 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_649 : heightPower (649 : Fin 988) ≤ ((2939388697213649 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_649
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_649 : heightFactor (649 : Fin 988) ≤ ((41186165875 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_649
  obtain ⟨hpl, hph⟩ := kernel_bounds_2490
  obtain ⟨hcl, hch⟩ := kernel_bounds_2491
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2491
  have h : (((6205081 / 2048 : ℚ) : ℝ) * (logKernel ((1245 / 32 : ℚ) : ℝ) - logKernel ((2491 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2491 / 64 : ℚ) : ℝ) + Real.log ((2491 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((41186165875 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_650 : ((263871868287657243 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((623 / 16 : ℚ) : ℝ) ∧
    Real.log ((623 / 16 : ℚ) : ℝ) ≤ ((131935934143828623 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((263871868287657243 / 72057594037927936 : ℚ) : ℝ) ≤ ((623 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((623 / 16 : ℚ) : ℝ) ≤ Real.exp ((131935934143828623 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_650 : heightPower (650 : Fin 988) ≤ ((2943899717828903 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_650
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_650 : heightFactor (650 : Fin 988) ≤ ((20082526949 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_650
  obtain ⟨hpl, hph⟩ := kernel_bounds_2491
  obtain ⟨hcl, hch⟩ := kernel_bounds_2492
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2492
  have h : (((388129 / 128 : ℚ) : ℝ) * (logKernel ((2491 / 64 : ℚ) : ℝ) - logKernel ((623 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((623 / 16 : ℚ) : ℝ) + Real.log ((623 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((20082526949 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_651 : ((263900778054960949 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2493 / 64 : ℚ) : ℝ) ∧
    Real.log ((2493 / 64 : ℚ) : ℝ) ≤ ((32987597256870119 / 9007199254740992 : ℚ) : ℝ) := by
  have hl : Real.exp ((263900778054960949 / 72057594037927936 : ℚ) : ℝ) ≤ ((2493 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2493 / 64 : ℚ) : ℝ) ≤ Real.exp ((32987597256870119 / 9007199254740992 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_651 : heightPower (651 : Fin 988) ≤ ((2948410693118537 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_651
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_651 : heightFactor (651 : Fin 988) ≤ ((9792310815 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_651
  obtain ⟨hpl, hph⟩ := kernel_bounds_2492
  obtain ⟨hcl, hch⟩ := kernel_bounds_2493
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2493
  have h : (((6215049 / 2048 : ℚ) : ℝ) * (logKernel ((623 / 16 : ℚ) : ℝ) - logKernel ((2493 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2493 / 64 : ℚ) : ℝ) + Real.log ((2493 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((9792310815 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_652 : ((263929676228212889 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1247 / 32 : ℚ) : ℝ) ∧
    Real.log ((1247 / 32 : ℚ) : ℝ) ≤ ((65982419057053223 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((263929676228212889 / 72057594037927936 : ℚ) : ℝ) ≤ ((1247 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1247 / 32 : ℚ) : ℝ) ≤ Real.exp ((65982419057053223 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_652 : heightPower (652 : Fin 988) ≤ ((1476460811559453 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_652
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_652 : heightFactor (652 : Fin 988) ≤ ((38198107417 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_652
  obtain ⟨hpl, hph⟩ := kernel_bounds_2493
  obtain ⟨hcl, hch⟩ := kernel_bounds_2494
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2494
  have h : (((1555009 / 512 : ℚ) : ℝ) * (logKernel ((2493 / 64 : ℚ) : ℝ) - logKernel ((1247 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1247 / 32 : ℚ) : ℝ) + Real.log ((1247 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((38198107417 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_653 : ((131979281408354377 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2495 / 64 : ℚ) : ℝ) ∧
    Real.log ((2495 / 64 : ℚ) : ℝ) ≤ ((263958562816708757 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((131979281408354377 / 36028797018963968 : ℚ) : ℝ) ≤ ((2495 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2495 / 64 : ℚ) : ℝ) ≤ Real.exp ((263958562816708757 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_653 : heightPower (653 : Fin 988) ≤ ((1478716253933161 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_653
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_653 : heightFactor (653 : Fin 988) ≤ ((582047427 / 4398046511104 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_653
  obtain ⟨hpl, hph⟩ := kernel_bounds_2494
  obtain ⟨hcl, hch⟩ := kernel_bounds_2495
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2495
  have h : (((6225025 / 2048 : ℚ) : ℝ) * (logKernel ((1247 / 32 : ℚ) : ℝ) - logKernel ((2495 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2495 / 64 : ℚ) : ℝ) + Real.log ((2495 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((582047427 / 4398046511104 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_654 : ((32998429728716633 / 9007199254740992 : ℚ) : ℝ) ≤ Real.log ((39 / 1 : ℚ) : ℝ) ∧
    Real.log ((39 / 1 : ℚ) : ℝ) ≤ ((263987437829733067 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((32998429728716633 / 9007199254740992 : ℚ) : ℝ) ≤ ((39 / 1 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((39 / 1 : ℚ) : ℝ) ≤ Real.exp ((263987437829733067 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_654 : heightPower (654 : Fin 988) ≤ ((740485836849263 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_654
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_654 : heightFactor (654 : Fin 988) ≤ ((36327431077 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_654
  obtain ⟨hpl, hph⟩ := kernel_bounds_2495
  obtain ⟨hcl, hch⟩ := kernel_bounds_2496
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2496
  have h : (((3042 / 1 : ℚ) : ℝ) * (logKernel ((2495 / 64 : ℚ) : ℝ) - logKernel ((39 / 1 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((39 / 1 : ℚ) : ℝ) + Real.log ((39 / 1 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((36327431077 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_655 : ((264016301276559177 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2497 / 64 : ℚ) : ℝ) ∧
    Real.log ((2497 / 64 : ℚ) : ℝ) ≤ ((66004075319139795 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((264016301276559177 / 72057594037927936 : ℚ) : ℝ) ≤ ((2497 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2497 / 64 : ℚ) : ℝ) ≤ Real.exp ((66004075319139795 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_655 : heightPower (655 : Fin 988) ≤ ((2966454141747321 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_655
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_655 : heightFactor (655 : Fin 988) ≤ ((8856678373 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_655
  obtain ⟨hpl, hph⟩ := kernel_bounds_2496
  obtain ⟨hcl, hch⟩ := kernel_bounds_2497
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2497
  have h : (((6235009 / 2048 : ℚ) : ℝ) * (logKernel ((39 / 1 : ℚ) : ℝ) - logKernel ((2497 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2497 / 64 : ℚ) : ℝ) + Real.log ((2497 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((8856678373 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_656 : ((264045153166449315 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((1249 / 32 : ℚ) : ℝ) ∧
    Real.log ((1249 / 32 : ℚ) : ℝ) ≤ ((132022576583224659 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((264045153166449315 / 72057594037927936 : ℚ) : ℝ) ≤ ((1249 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1249 / 32 : ℚ) : ℝ) ≤ Real.exp ((132022576583224659 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_656 : heightPower (656 : Fin 988) ≤ ((742741222738327 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_656
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_656 : heightFactor (656 : Fin 988) ≤ ((34548315789 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_656
  obtain ⟨hpl, hph⟩ := kernel_bounds_2497
  obtain ⟨hcl, hch⟩ := kernel_bounds_2498
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2498
  have h : (((1560001 / 512 : ℚ) : ℝ) * (logKernel ((2497 / 64 : ℚ) : ℝ) - logKernel ((1249 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1249 / 32 : ℚ) : ℝ) + Real.log ((1249 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((34548315789 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_657 : ((132036996754327289 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2499 / 64 : ℚ) : ℝ) ∧
    Real.log ((2499 / 64 : ℚ) : ℝ) ≤ ((264073993508654581 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((132036996754327289 / 36028797018963968 : ℚ) : ℝ) ≤ ((2499 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2499 / 64 : ℚ) : ℝ) ≤ Real.exp ((264073993508654581 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_657 : heightPower (657 : Fin 988) ≤ ((2975475595051151 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_657
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_657 : heightFactor (657 : Fin 988) ≤ ((33691685209 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_657
  obtain ⟨hpl, hph⟩ := kernel_bounds_2498
  obtain ⟨hcl, hch⟩ := kernel_bounds_2499
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2499
  have h : (((6245001 / 2048 : ℚ) : ℝ) * (logKernel ((1249 / 32 : ℚ) : ℝ) - logKernel ((2499 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2499 / 64 : ℚ) : ℝ) + Real.log ((2499 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((33691685209 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_658 : ((264102822312414963 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((625 / 16 : ℚ) : ℝ) ∧
    Real.log ((625 / 16 : ℚ) : ℝ) ≤ ((132051411156207483 / 36028797018963968 : ℚ) : ℝ) := by
  have hl : Real.exp ((264102822312414963 / 72057594037927936 : ℚ) : ℝ) ≤ ((625 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((625 / 16 : ℚ) : ℝ) ≤ Real.exp ((132051411156207483 / 36028797018963968 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_658 : heightPower (658 : Fin 988) ≤ ((186249140879809 / 17592186044416 : ℚ) : ℝ) := by
  have hh := log_height_bounds_658
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_658 : heightFactor (658 : Fin 988) ≤ ((16428141337 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_658
  obtain ⟨hpl, hph⟩ := kernel_bounds_2499
  obtain ⟨hcl, hch⟩ := kernel_bounds_2500
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2500
  have h : (((390625 / 128 : ℚ) : ℝ) * (logKernel ((2499 / 64 : ℚ) : ℝ) - logKernel ((625 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((625 / 16 : ℚ) : ℝ) + Real.log ((625 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((16428141337 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_659 : ((132065819793479689 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2501 / 64 : ℚ) : ℝ) ∧
    Real.log ((2501 / 64 : ℚ) : ℝ) ≤ ((264131639586959381 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((132065819793479689 / 36028797018963968 : ℚ) : ℝ) ≤ ((2501 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2501 / 64 : ℚ) : ℝ) ≤ Real.exp ((264131639586959381 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_659 : heightPower (659 : Fin 988) ≤ ((1492248434033369 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_659
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_659 : heightFactor (659 : Fin 988) ≤ ((16020791225 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_659
  obtain ⟨hpl, hph⟩ := kernel_bounds_2500
  obtain ⟨hcl, hch⟩ := kernel_bounds_2501
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2501
  have h : (((6255001 / 2048 : ℚ) : ℝ) * (logKernel ((625 / 16 : ℚ) : ℝ) - logKernel ((2501 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2501 / 64 : ℚ) : ℝ) + Real.log ((2501 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((16020791225 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_660 : ((66040111335376417 / 18014398509481984 : ℚ) : ℝ) ≤ Real.log ((1251 / 32 : ℚ) : ℝ) ∧
    Real.log ((1251 / 32 : ℚ) : ℝ) ≤ ((264160445341505671 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((66040111335376417 / 18014398509481984 : ℚ) : ℝ) ≤ ((1251 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1251 / 32 : ℚ) : ℝ) ≤ Real.exp ((264160445341505671 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_660 : heightPower (660 : Fin 988) ≤ ((1494503718528269 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_660
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_660 : heightFactor (660 : Fin 988) ≤ ((15623535907 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_660
  obtain ⟨hpl, hph⟩ := kernel_bounds_2501
  obtain ⟨hcl, hch⟩ := kernel_bounds_2502
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2502
  have h : (((1565001 / 512 : ℚ) : ℝ) * (logKernel ((2501 / 64 : ℚ) : ℝ) - logKernel ((1251 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1251 / 32 : ℚ) : ℝ) + Real.log ((1251 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((15623535907 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_661 : ((16511827474078789 / 4503599627370496 : ℚ) : ℝ) ≤ Real.log ((2503 / 64 : ℚ) : ℝ) ∧
    Real.log ((2503 / 64 : ℚ) : ℝ) ≤ ((264189239585260627 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((16511827474078789 / 4503599627370496 : ℚ) : ℝ) ≤ ((2503 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2503 / 64 : ℚ) : ℝ) ≤ Real.exp ((264189239585260627 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_661 : heightPower (661 : Fin 988) ≤ ((1496758980541155 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_661
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_661 : heightFactor (661 : Fin 988) ≤ ((30472250733 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_661
  obtain ⟨hpl, hph⟩ := kernel_bounds_2502
  obtain ⟨hcl, hch⟩ := kernel_bounds_2503
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2503
  have h : (((6265009 / 2048 : ℚ) : ℝ) * (logKernel ((1251 / 32 : ℚ) : ℝ) - logKernel ((2503 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2503 / 64 : ℚ) : ℝ) + Real.log ((2503 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((30472250733 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_662 : ((132109011163710003 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((313 / 8 : ℚ) : ℝ) ∧
    Real.log ((313 / 8 : ℚ) : ℝ) ≤ ((264218022327420009 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((132109011163710003 / 36028797018963968 : ℚ) : ℝ) ≤ ((313 / 8 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((313 / 8 : ℚ) : ℝ) ≤ Real.exp ((264218022327420009 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_662 : heightPower (662 : Fin 988) ≤ ((1499014220089987 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_662
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_662 : heightFactor (662 : Fin 988) ≤ ((29716631551 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_662
  obtain ⟨hpl, hph⟩ := kernel_bounds_2503
  obtain ⟨hcl, hch⟩ := kernel_bounds_2504
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2504
  have h : (((97969 / 32 : ℚ) : ℝ) * (logKernel ((2503 / 64 : ℚ) : ℝ) - logKernel ((313 / 8 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((313 / 8 : ℚ) : ℝ) + Real.log ((313 / 8 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((29716631551 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_663 : ((264246793577168557 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2505 / 64 : ℚ) : ℝ) ∧
    Real.log ((2505 / 64 : ℚ) : ℝ) ≤ ((16515424598573035 / 4503599627370496 : ℚ) : ℝ) := by
  have hl : Real.exp ((264246793577168557 / 72057594037927936 : ℚ) : ℝ) ≤ ((2505 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2505 / 64 : ℚ) : ℝ) ≤ Real.exp ((16515424598573035 / 4503599627370496 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_663 : heightPower (663 : Fin 988) ≤ ((2932166869517 / 274877906944 : ℚ) : ℝ) := by
  have hh := log_height_bounds_663
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_663 : heightFactor (663 : Fin 988) ≤ ((7244934671 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_663
  obtain ⟨hpl, hph⟩ := kernel_bounds_2504
  obtain ⟨hcl, hch⟩ := kernel_bounds_2505
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2505
  have h : (((6275025 / 2048 : ℚ) : ℝ) * (logKernel ((313 / 8 : ℚ) : ℝ) - logKernel ((2505 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2505 / 64 : ℚ) : ℝ) + Real.log ((2505 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((7244934671 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_664 : ((33034444167960003 / 9007199254740992 : ℚ) : ℝ) ≤ Real.log ((1253 / 32 : ℚ) : ℝ) ∧
    Real.log ((1253 / 32 : ℚ) : ℝ) ≤ ((264275553343680027 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((33034444167960003 / 9007199254740992 : ℚ) : ℝ) ≤ ((1253 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1253 / 32 : ℚ) : ℝ) ≤ Real.exp ((264275553343680027 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_664 : heightPower (664 : Fin 988) ≤ ((187940578983403 / 17592186044416 : ℚ) : ℝ) := by
  have hh := log_height_bounds_664
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_664 : heightFactor (664 : Fin 988) ≤ ((14130554159 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_664
  obtain ⟨hpl, hph⟩ := kernel_bounds_2505
  obtain ⟨hcl, hch⟩ := kernel_bounds_2506
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2506
  have h : (((1570009 / 512 : ℚ) : ℝ) * (logKernel ((2505 / 64 : ℚ) : ℝ) - logKernel ((1253 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1253 / 32 : ℚ) : ℝ) + Real.log ((1253 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((14130554159 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_665 : ((33038037704514647 / 9007199254740992 : ℚ) : ℝ) ≤ Real.log ((2507 / 64 : ℚ) : ℝ) ∧
    Real.log ((2507 / 64 : ℚ) : ℝ) ≤ ((264304301636117179 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((33038037704514647 / 9007199254740992 : ℚ) : ℝ) ≤ ((2507 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2507 / 64 : ℚ) : ℝ) ≤ Real.exp ((264304301636117179 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_665 : heightPower (665 : Fin 988) ≤ ((752889902065721 / 70368744177664 : ℚ) : ℝ) := by
  have hh := log_height_bounds_665
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_665 : heightFactor (665 : Fin 988) ≤ ((3445036015 / 35184372088832 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_665
  obtain ⟨hpl, hph⟩ := kernel_bounds_2506
  obtain ⟨hcl, hch⟩ := kernel_bounds_2507
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2507
  have h : (((6285049 / 2048 : ℚ) : ℝ) * (logKernel ((1253 / 32 : ℚ) : ℝ) - logKernel ((2507 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2507 / 64 : ℚ) : ℝ) + Real.log ((2507 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((3445036015 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_666 : ((132166519231815907 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((627 / 16 : ℚ) : ℝ) ∧
    Real.log ((627 / 16 : ℚ) : ℝ) ≤ ((264333038463631817 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((132166519231815907 / 36028797018963968 : ℚ) : ℝ) ≤ ((627 / 16 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((627 / 16 : ℚ) : ℝ) ≤ Real.exp ((264333038463631817 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_666 : heightPower (666 : Fin 988) ≤ ((3016069908006467 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_666
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_666 : heightFactor (666 : Fin 988) ≤ ((13438418477 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_666
  obtain ⟨hpl, hph⟩ := kernel_bounds_2507
  obtain ⟨hcl, hch⟩ := kernel_bounds_2508
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2508
  have h : (((393129 / 128 : ℚ) : ℝ) * (logKernel ((2507 / 64 : ℚ) : ℝ) - logKernel ((627 / 16 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((627 / 16 : ℚ) : ℝ) + Real.log ((627 / 16 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((13438418477 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_667 : ((264361763835364801 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((2509 / 64 : ℚ) : ℝ) ∧
    Real.log ((2509 / 64 : ℚ) : ℝ) ≤ ((66090440958841201 / 18014398509481984 : ℚ) : ℝ) := by
  have hl : Real.exp ((264361763835364801 / 72057594037927936 : ℚ) : ℝ) ≤ ((2509 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2509 / 64 : ℚ) : ℝ) ≤ Real.exp ((66090440958841201 / 18014398509481984 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_667 : heightPower (667 : Fin 988) ≤ ((3020580163000903 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_667
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_667 : heightFactor (667 : Fin 988) ≤ ((6552581151 / 70368744177664 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_667
  obtain ⟨hpl, hph⟩ := kernel_bounds_2508
  obtain ⟨hcl, hch⟩ := kernel_bounds_2509
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2509
  have h : (((6295081 / 2048 : ℚ) : ℝ) * (logKernel ((627 / 16 : ℚ) : ℝ) - logKernel ((2509 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2509 / 64 : ℚ) : ℝ) + Real.log ((2509 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((6552581151 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_668 : ((132195238880223033 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((1255 / 32 : ℚ) : ℝ) ∧
    Real.log ((1255 / 32 : ℚ) : ℝ) ≤ ((264390477760446069 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((132195238880223033 / 36028797018963968 : ℚ) : ℝ) ≤ ((1255 / 32 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((1255 / 32 : ℚ) : ℝ) ≤ Real.exp ((264390477760446069 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_668 : heightPower (668 : Fin 988) ≤ ((47267037082529 / 4398046511104 : ℚ) : ℝ) := by
  have hh := log_height_bounds_668
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_668 : heightFactor (668 : Fin 988) ≤ ((25560331503 / 281474976710656 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_668
  obtain ⟨hpl, hph⟩ := kernel_bounds_2509
  obtain ⟨hcl, hch⟩ := kernel_bounds_2510
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2510
  have h : (((1575025 / 512 : ℚ) : ℝ) * (logKernel ((2509 / 64 : ℚ) : ℝ) - logKernel ((1255 / 32 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((1255 / 32 : ℚ) : ℝ) + Real.log ((1255 / 32 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((25560331503 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_669 : ((33052397530999329 / 9007199254740992 : ℚ) : ℝ) ≤ Real.log ((2511 / 64 : ℚ) : ℝ) ∧
    Real.log ((2511 / 64 : ℚ) : ℝ) ≤ ((264419180247994635 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((33052397530999329 / 9007199254740992 : ℚ) : ℝ) ≤ ((2511 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2511 / 64 : ℚ) : ℝ) ≤ Real.exp ((264419180247994635 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_669 : heightPower (669 : Fin 988) ≤ ((3029600538884947 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_669
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_669 : heightFactor (669 : Fin 988) ≤ ((12463224235 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_669
  obtain ⟨hpl, hph⟩ := kernel_bounds_2510
  obtain ⟨hcl, hch⟩ := kernel_bounds_2511
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2511
  have h : (((6305121 / 2048 : ℚ) : ℝ) * (logKernel ((1255 / 32 : ℚ) : ℝ) - logKernel ((2511 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2511 / 64 : ℚ) : ℝ) + Real.log ((2511 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((12463224235 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_670 : ((264447871307118629 / 72057594037927936 : ℚ) : ℝ) ≤ Real.log ((157 / 4 : ℚ) : ℝ) ∧
    Real.log ((157 / 4 : ℚ) : ℝ) ≤ ((33055983913389829 / 9007199254740992 : ℚ) : ℝ) := by
  have hl : Real.exp ((264447871307118629 / 72057594037927936 : ℚ) : ℝ) ≤ ((157 / 4 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((157 / 4 : ℚ) : ℝ) ≤ Real.exp ((33055983913389829 / 9007199254740992 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_670 : heightPower (670 : Fin 988) ≤ ((1517055329922877 / 140737488355328 : ℚ) : ℝ) := by
  have hh := log_height_bounds_670
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_670 : heightFactor (670 : Fin 988) ≤ ((12154138227 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_670
  obtain ⟨hpl, hph⟩ := kernel_bounds_2511
  obtain ⟨hcl, hch⟩ := kernel_bounds_2512
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2512
  have h : (((24649 / 8 : ℚ) : ℝ) * (logKernel ((2511 / 64 : ℚ) : ℝ) - logKernel ((157 / 4 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((157 / 4 : ℚ) : ℝ) + Real.log ((157 / 4 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((12154138227 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

theorem log_height_bounds_671 : ((132238275473457655 / 36028797018963968 : ℚ) : ℝ) ≤ Real.log ((2513 / 64 : ℚ) : ℝ) ∧
    Real.log ((2513 / 64 : ℚ) : ℝ) ≤ ((264476550946915313 / 72057594037927936 : ℚ) : ℝ) := by
  have hl : Real.exp ((132238275473457655 / 36028797018963968 : ℚ) : ℝ) ≤ ((2513 / 64 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  have hh : ((2513 / 64 : ℚ) : ℝ) ≤ Real.exp ((264476550946915313 / 72057594037927936 : ℚ) : ℝ) := by dyadic_interval [prec := 80]
  constructor
  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl
  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh
theorem height_power_upper_671 : heightPower (671 : Fin 988) ≤ ((3038620736199813 / 281474976710656 : ℚ) : ℝ) := by
  have hh := log_height_bounds_671
  norm_num [heightPower, heightV, height, shiftV] at *
  linarith
theorem height_factor_upper_671 : heightFactor (671 : Fin 988) ≤ ((11852713141 / 140737488355328 : ℚ) : ℝ) := by
  obtain ⟨hll, hlh⟩ := log_height_bounds_671
  obtain ⟨hpl, hph⟩ := kernel_bounds_2512
  obtain ⟨hcl, hch⟩ := kernel_bounds_2513
  obtain ⟨hzl, hzh⟩ := height_z_bounds_2513
  have h : (((6315169 / 2048 : ℚ) : ℝ) * (logKernel ((157 / 4 : ℚ) : ℝ) - logKernel ((2513 / 64 : ℚ) : ℝ))) *
      Real.exp (((1 / 3 : ℚ) : ℝ) * (((2513 / 64 : ℚ) : ℝ) + Real.log ((2513 / 64 : ℚ) : ℝ) - ((2057 / 64 : ℚ) : ℝ))) ≤ ((11852713141 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 80]
  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,
    height, shiftP, shiftV] at h ⊢
  nlinarith only [h]

end LegendreK6.M2Pilot.Enclosures.Height020
