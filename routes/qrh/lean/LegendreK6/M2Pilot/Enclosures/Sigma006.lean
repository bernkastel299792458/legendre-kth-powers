import LegendreK6.M2PilotDefinitions
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp

/-! Generated proposals: every bound is checked by Lean, not by trusting Arb. -/
namespace LegendreK6.M2Pilot.Enclosures.Sigma006
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem sigma_factor_upper_768 : sigmaFactor (768 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-3768435 / 114688 : ℚ) : ℝ) - Real.exp ((-3685 / 112 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_768 : sigmaPower (768 : Fin 1536) ≤ ((107228562556441 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_769 : sigmaFactor (769 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-1445490123 / 44032000 : ℚ) : ℝ) - Real.exp ((-2894823371 / 88064000 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_769 : sigmaPower (769 : Fin 1536) ≤ ((53554432778189 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_770 : sigmaFactor (770 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-1443901921 / 44023808 : ℚ) : ℝ) - Real.exp ((-722911563 / 22011904 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_770 : sigmaPower (770 : Fin 1536) ≤ ((13373640501201 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_771 : sigmaFactor (771 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-240385739 / 7335936 : ℚ) : ℝ) - Real.exp ((-962823521 / 29343744 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_771 : sigmaPower (771 : Fin 1536) ≤ ((26717334472815 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_772 : sigmaFactor (772 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-42374343 / 1294336 : ℚ) : ℝ) - Real.exp ((-10607707 / 323584 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_772 : sigmaPower (772 : Fin 1536) ≤ ((53374753588221 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_773 : sigmaFactor (773 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-1439141605 / 43999232 : ℚ) : ℝ) - Real.exp ((-2882123475 / 87998464 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_773 : sigmaPower (773 : Fin 1536) ≤ ((26657407960061 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_774 : sigmaFactor (774 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-479185421 / 14663680 : ℚ) : ℝ) - Real.exp ((-239912673 / 7331840 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_774 : sigmaPower (774 : Fin 1536) ≤ ((53254855928869 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_775 : sigmaFactor (775 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-358992909 / 10995712 : ℚ) : ℝ) - Real.exp ((-2875782107 / 87965696 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_775 : sigmaPower (775 : Fin 1536) ≤ ((106389747203979 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_776 : sigmaFactor (776 : Fin 1536) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-32599721 / 999424 : ℚ) : ℝ) - Real.exp ((-4080417 / 124928 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_776 : sigmaPower (776 : Fin 1536) ≤ ((106269737853999 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_777 : sigmaFactor (777 : Fin 1536) ≤ ((1 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-477601509 / 14655488 : ℚ) : ℝ) - Real.exp ((-956482153 / 29310976 : ℚ) : ℝ)) ≤ ((1 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_777 : sigmaPower (777 : Fin 1536) ≤ ((106149683782815 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_778 : sigmaFactor (778 : Fin 1536) ≤ ((1 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-1431222045 / 43958272 : ℚ) : ℝ) - Real.exp ((-716570195 / 21979136 : ℚ) : ℝ)) ≤ ((1 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_778 : sigmaPower (778 : Fin 1536) ≤ ((53014792482713 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_779 : sigmaFactor (779 : Fin 1536) ≤ ((1 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-714820139 / 21975040 : ℚ) : ℝ) - Real.exp ((-2863116531 / 87900160 : ℚ) : ℝ)) ≤ ((1 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_779 : sigmaPower (779 : Fin 1536) ≤ ((105909441376809 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_780 : sigmaFactor (780 : Fin 1536) ≤ ((1 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-238009871 / 7323648 : ℚ) : ℝ) - Real.exp ((-59582369 / 1830912 : ℚ) : ℝ)) ≤ ((1 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_780 : sigmaPower (780 : Fin 1536) ≤ ((105789252991925 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_781 : sigmaFactor (781 : Fin 1536) ≤ ((1 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-1426478889 / 43933696 : ℚ) : ℝ) - Real.exp ((-2856792323 / 87867392 : ℚ) : ℝ)) ≤ ((1 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_781 : sigmaPower (781 : Fin 1536) ≤ ((105669019785715 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_782 : sigmaFactor (782 : Fin 1536) ≤ ((1 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-1424899267 / 43925504 : ℚ) : ℝ) - Real.exp ((-713408091 / 21962752 : ℚ) : ℝ)) ≤ ((1 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_782 : sigmaPower (782 : Fin 1536) ≤ ((52774370866551 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_783 : sigmaFactor (783 : Fin 1536) ≤ ((1 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-59305015 / 1829888 : ℚ) : ℝ) - Real.exp ((-950157945 / 29278208 : ℚ) : ℝ)) ≤ ((1 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_783 : sigmaPower (783 : Fin 1536) ≤ ((105428418808991 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_784 : sigmaFactor (784 : Fin 1536) ≤ ((1 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-177717771 / 5488640 : ℚ) : ℝ) - Real.exp ((-11122331 / 343040 : ℚ) : ℝ)) ≤ ((1 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_784 : sigmaPower (784 : Fin 1536) ≤ ((52654025494133 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_785 : sigmaFactor (785 : Fin 1536) ≤ ((1 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-1420164691 / 43900928 : ℚ) : ℝ) - Real.exp ((-2844161067 / 87801856 : ℚ) : ℝ)) ≤ ((1 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_785 : sigmaPower (785 : Fin 1536) ≤ ((52593819122897 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_786 : sigmaFactor (786 : Fin 1536) ≤ ((1 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-472862643 / 14630912 : ℚ) : ℝ) - Real.exp ((-236750569 / 7315456 : ℚ) : ℝ)) ≤ ((1 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_786 : sigmaPower (786 : Fin 1536) ≤ ((105067180556423 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_787 : sigmaFactor (787 : Fin 1536) ≤ ((1 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-64409631 / 1994752 : ℚ) : ℝ) - Real.exp ((-257986729 / 7979008 : ℚ) : ℝ)) ≤ ((1 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_787 : sigmaPower (787 : Fin 1536) ≤ ((52473338947491 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_788 : sigmaFactor (788 : Fin 1536) ≤ ((1 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-707718275 / 21938176 : ℚ) : ℝ) - Real.exp ((-177168915 / 5484544 : ℚ) : ℝ)) ≤ ((1 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_788 : sigmaPower (788 : Fin 1536) ≤ ((52413065118141 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_789 : sigmaFactor (789 : Fin 1536) ≤ ((1 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-27722783 / 860160 : ℚ) : ℝ) - Real.exp ((-55520641 / 1720320 : ℚ) : ℝ)) ≤ ((1 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_789 : sigmaPower (789 : Fin 1536) ≤ ((104705537555113 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_790 : sigmaFactor (790 : Fin 1536) ≤ ((1 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-1412288031 / 43859968 : ℚ) : ℝ) - Real.exp ((-707101043 / 21929984 : ℚ) : ℝ)) ≤ ((1 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_790 : sigmaPower (790 : Fin 1536) ≤ ((13073112478281 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_791 : sigmaFactor (791 : Fin 1536) ≤ ((1 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-352678711 / 10962944 : ℚ) : ℝ) - Real.exp ((-2825257083 / 87703552 : ℚ) : ℝ)) ≤ ((1 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_791 : sigmaPower (791 : Fin 1536) ≤ ((52232108512221 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_792 : sigmaFactor (792 : Fin 1536) ≤ ((1 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-117428531 / 3653632 : ℚ) : ℝ) - Real.exp ((-14698497 / 456704 : ℚ) : ℝ)) ≤ ((1 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_792 : sigmaPower (792 : Fin 1536) ≤ ((104343489124429 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_793 : sigmaFactor (793 : Fin 1536) ≤ ((1 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-1407570615 / 43835392 : ℚ) : ℝ) - Real.exp ((-2818967195 / 87670784 : ℚ) : ℝ)) ≤ ((1 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_793 : sigmaPower (793 : Fin 1536) ≤ ((104222716100925 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_794 : sigmaFactor (794 : Fin 1536) ≤ ((1 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-1405999573 / 43827200 : ℚ) : ℝ) - Real.exp ((-703956099 / 21913600 : ℚ) : ℝ)) ≤ ((1 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_794 : sigmaPower (794 : Fin 1536) ≤ ((104101897928627 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_795 : sigmaFactor (795 : Fin 1536) ≤ ((1 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-234071541 / 7303168 : ℚ) : ℝ) - Real.exp ((-937561009 / 29212672 : ℚ) : ℝ)) ≤ ((1 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_795 : sigmaPower (795 : Fin 1536) ≤ ((103981034582213 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_796 : sigmaFactor (796 : Fin 1536) ≤ ((1 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-701429817 / 21905408 : ℚ) : ℝ) - Real.exp ((-175596443 / 5476352 : ℚ) : ℝ)) ≤ ((1 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_796 : sigmaPower (796 : Fin 1536) ≤ ((103860126036343 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_797 : sigmaFactor (797 : Fin 1536) ≤ ((1 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-1401290737 / 43802624 : ℚ) : ℝ) - Real.exp ((-2806404579 / 87605248 : ℚ) : ℝ)) ≤ ((1 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_797 : sigmaPower (797 : Fin 1536) ≤ ((103739172265657 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_798 : sigmaFactor (798 : Fin 1536) ≤ ((1 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-42415835 / 1327104 : ℚ) : ℝ) - Real.exp ((-21236875 / 663552 : ℚ) : ℝ)) ≤ ((1 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_798 : sigmaPower (798 : Fin 1536) ≤ ((12952271655597 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_799 : sigmaFactor (799 : Fin 1536) ≤ ((1 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-87384693 / 2736640 : ℚ) : ℝ) - Real.exp ((-2800131851 / 87572480 : ℚ) : ℝ)) ≤ ((1 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_799 : sigmaPower (799 : Fin 1536) ≤ ((103497128948303 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_800 : sigmaFactor (800 : Fin 1536) ≤ ((3 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-87286771 / 2736128 : ℚ) : ℝ) - Real.exp ((-2731443 / 85504 : ℚ) : ℝ)) ≤ ((3 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_800 : sigmaPower (800 : Fin 1536) ≤ ((25844009837705 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_801 : sigmaFactor (801 : Fin 1536) ≤ ((3 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-465007433 / 14589952 : ℚ) : ℝ) - Real.exp ((-931288281 / 29179904 : ℚ) : ℝ)) ≤ ((3 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_801 : sigmaPower (801 : Fin 1536) ≤ ((103254904426893 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_802 : sigmaFactor (802 : Fin 1536) ≤ ((3 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-1393456977 / 43761664 : ℚ) : ℝ) - Real.exp ((-697683371 / 21880832 : ℚ) : ℝ)) ≤ ((3 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_802 : sigmaPower (802 : Fin 1536) ≤ ((51566862075533 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_803 : sigmaFactor (803 : Fin 1536) ≤ ((3 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-695946185 / 21876736 : ℚ) : ℝ) - Real.exp ((-2787603555 / 87506944 : ℚ) : ℝ)) ≤ ((3 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_803 : sigmaPower (803 : Fin 1536) ≤ ((103012498497865 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_804 : sigmaFactor (804 : Fin 1536) ≤ ((3 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-231721413 / 7290880 : ℚ) : ℝ) - Real.exp ((-58009897 / 1822720 : ℚ) : ℝ)) ≤ ((3 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_804 : sigmaPower (804 : Fin 1536) ≤ ((51445613720899 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_805 : sigmaFactor (805 : Fin 1536) ≤ ((3 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-1388765301 / 43737088 : ℚ) : ℝ) - Real.exp ((-2781347987 / 87474176 : ℚ) : ℝ)) ≤ ((3 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_805 : sigmaPower (805 : Fin 1536) ≤ ((102769910957353 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_806 : sigmaFactor (806 : Fin 1536) ≤ ((3 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-81600167 / 2572288 : ℚ) : ℝ) - Real.exp ((-40856211 / 1286144 : ℚ) : ℝ)) ≤ ((3 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_806 : sigmaPower (806 : Fin 1536) ≤ ((51324274509499 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_807 : sigmaFactor (807 : Fin 1536) ≤ ((3 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-115470091 / 3643392 : ℚ) : ℝ) - Real.exp ((-925032713 / 29147136 : ℚ) : ℝ)) ≤ ((3 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_807 : sigmaPower (807 : Fin 1536) ≤ ((3203973175037 / 8796093022208 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_808 : sigmaFactor (808 : Fin 1536) ≤ ((3 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-346020015 / 10928128 : ℚ) : ℝ) - Real.exp ((-43312115 / 1366016 : ℚ) : ℝ)) ≤ ((3 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_808 : sigmaPower (808 : Fin 1536) ≤ ((25601422169585 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_809 : sigmaFactor (809 : Fin 1536) ≤ ((3 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-125683613 / 3973120 : ℚ) : ℝ) - Real.exp ((-251714001 / 7946240 : ℚ) : ℝ)) ≤ ((3 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_809 : sigmaPower (809 : Fin 1536) ≤ ((102284190224879 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_810 : sigmaFactor (810 : Fin 1536) ≤ ((3 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-460320047 / 14565376 : ℚ) : ℝ) - Real.exp ((-230477841 / 7282688 : ℚ) : ℝ)) ≤ ((3 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_810 : sigmaPower (810 : Fin 1536) ≤ ((12770330776899 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_811 : sigmaFactor (811 : Fin 1536) ≤ ((3 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-689700627 / 21843968 : ℚ) : ℝ) - Real.exp ((-2762615603 / 87375872 : ℚ) : ℝ)) ≤ ((3 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_811 : sigmaPower (811 : Fin 1536) ≤ ((25510264155913 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_812 : sigmaFactor (812 : Fin 1536) ≤ ((3 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-688921541 / 21839872 : ℚ) : ℝ) - Real.exp ((-172468659 / 5459968 : ℚ) : ℝ)) ≤ ((3 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_812 : sigmaPower (812 : Fin 1536) ≤ ((50959710712307 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_813 : sigmaFactor (813 : Fin 1536) ≤ ((3 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-458761875 / 14557184 : ℚ) : ℝ) - Real.exp ((-918794305 / 29114368 : ℚ) : ℝ)) ≤ ((3 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_813 : sigmaPower (813 : Fin 1536) ≤ ((25449435148103 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_814 : sigmaFactor (814 : Fin 1536) ≤ ((1 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-1374728883 / 43663360 : ℚ) : ℝ) - Real.exp ((-688317179 / 21831680 : ℚ) : ℝ)) ≤ ((1 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_814 : sigmaPower (814 : Fin 1536) ≤ ((101676014101361 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_815 : sigmaFactor (815 : Fin 1536) ≤ ((1 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-171646607 / 5456896 : ℚ) : ℝ) - Real.exp ((-2750155947 / 87310336 : ℚ) : ℝ)) ≤ ((1 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_815 : sigmaPower (815 : Fin 1536) ≤ ((101554241925757 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_816 : sigmaFactor (816 : Fin 1536) ≤ ((1 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-57150731 / 1818624 : ℚ) : ℝ) - Real.exp ((-3576881 / 113664 : ℚ) : ℝ)) ≤ ((1 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_816 : sigmaPower (816 : Fin 1536) ≤ ((101432424039877 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_817 : sigmaFactor (817 : Fin 1536) ≤ ((1 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-1370062947 / 43638784 : ℚ) : ℝ) - Real.exp ((-2743934699 / 87277568 : ℚ) : ℝ)) ≤ ((1 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_817 : sigmaPower (817 : Fin 1536) ≤ ((50655280208989 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_818 : sigmaFactor (818 : Fin 1536) ≤ ((1 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-1368509065 / 43630592 : ℚ) : ℝ) - Real.exp ((-685206555 / 21815296 : ℚ) : ℝ)) ≤ ((1 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_818 : sigmaPower (818 : Fin 1536) ≤ ((50594325517149 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_819 : sigmaFactor (819 : Fin 1536) ≤ ((1 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-227825983 / 7270400 : ℚ) : ℝ) - Real.exp ((-912573057 / 29081600 : ℚ) : ℝ)) ≤ ((1 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_819 : sigmaPower (819 : Fin 1536) ≤ ((101066695863057 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_820 : sigmaFactor (820 : Fin 1536) ≤ ((1 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-5642163 / 180224 : ℚ) : ℝ) - Real.exp ((-1412507 / 45056 : ℚ) : ℝ)) ≤ ((1 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_820 : sigmaPower (820 : Fin 1536) ≤ ((100944694878453 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_821 : sigmaFactor (821 : Fin 1536) ≤ ((1 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-1363851709 / 43606016 : ℚ) : ℝ) - Real.exp ((-2731509363 / 87212032 : ℚ) : ℝ)) ≤ ((1 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_821 : sigmaPower (821 : Fin 1536) ≤ ((50411324027333 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_822 : sigmaFactor (822 : Fin 1536) ≤ ((1 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-454100229 / 14532608 : ℚ) : ℝ) - Real.exp ((-227367217 / 7266304 : ℚ) : ℝ)) ≤ ((1 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_822 : sigmaPower (822 : Fin 1536) ≤ ((100700555365857 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_823 : sigmaFactor (823 : Fin 1536) ≤ ((5 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-20011035 / 641024 : ℚ) : ℝ) - Real.exp ((-160312075 / 5128192 : ℚ) : ℝ)) ≤ ((5 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_823 : sigmaPower (823 : Fin 1536) ≤ ((100578416786167 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_824 : sigmaFactor (824 : Fin 1536) ≤ ((5 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-339800197 / 10895360 : ℚ) : ℝ) - Real.exp ((-42534459 / 1361920 : ℚ) : ℝ)) ≤ ((5 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_824 : sigmaPower (824 : Fin 1536) ≤ ((50228116144859 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_825 : sigmaFactor (825 : Fin 1536) ≤ ((5 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-452550637 / 14524416 : ℚ) : ℝ) - Real.exp ((-906368969 / 29048832 : ℚ) : ℝ)) ≤ ((5 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_825 : sigmaPower (825 : Fin 1536) ≤ ((25083500462653 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_826 : sigmaFactor (826 : Fin 1536) ≤ ((5 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-1356103749 / 43565056 : ℚ) : ℝ) - Real.exp ((-679002467 / 21782528 : ℚ) : ℝ)) ≤ ((5 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_826 : sigmaPower (826 : Fin 1536) ≤ ((25052931360733 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_827 : sigmaFactor (827 : Fin 1536) ≤ ((5 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-677278151 / 21778432 : ℚ) : ℝ) - Real.exp ((-2712914259 / 87113728 : ℚ) : ℝ)) ≤ ((5 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_827 : sigmaPower (827 : Fin 1536) ≤ ((25022350760185 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_828 : sigmaFactor (828 : Fin 1536) ≤ ((5 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-225501595 / 7258112 : ℚ) : ℝ) - Real.exp ((-56454585 / 1814528 : ℚ) : ℝ)) ≤ ((5 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_828 : sigmaPower (828 : Fin 1536) ≤ ((99967034618081 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_829 : sigmaFactor (829 : Fin 1536) ≤ ((5 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-1351463553 / 43540480 : ℚ) : ℝ) - Real.exp ((-2706727331 / 87080960 : ℚ) : ℝ)) ≤ ((5 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_829 : sigmaPower (829 : Fin 1536) ≤ ((24961155037245 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_830 : sigmaFactor (830 : Fin 1536) ≤ ((5 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-1349918251 / 43532288 : ℚ) : ℝ) - Real.exp ((-675909003 / 21766144 : ℚ) : ℝ)) ≤ ((5 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_830 : sigmaPower (830 : Fin 1536) ≤ ((99722159607439 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_831 : sigmaFactor (831 : Fin 1536) ≤ ((3 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-1276869 / 41216 : ℚ) : ℝ) - Real.exp ((-81834731 / 2637824 : ℚ) : ℝ)) ≤ ((3 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_831 : sigmaPower (831 : Fin 1536) ≤ ((99599652967445 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_832 : sigmaFactor (832 : Fin 1536) ≤ ((3 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-42088431 / 1359872 : ℚ) : ℝ) - Real.exp ((-658559 / 21248 : ℚ) : ℝ)) ≤ ((3 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_832 : sigmaPower (832 : Fin 1536) ≤ ((99477100202963 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_833 : sigmaFactor (833 : Fin 1536) ≤ ((3 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-1345286635 / 43507712 : ℚ) : ℝ) - Real.exp ((-2694370635 / 87015424 : ℚ) : ℝ)) ≤ ((3 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_833 : sigmaPower (833 : Fin 1536) ≤ ((99354501287939 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_834 : sigmaFactor (834 : Fin 1536) ≤ ((3 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-447914731 / 14499840 : ℚ) : ℝ) - Real.exp ((-224273753 / 7249920 : ℚ) : ℝ)) ≤ ((3 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_834 : sigmaPower (834 : Fin 1536) ≤ ((24807964049075 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_835 : sigmaFactor (835 : Fin 1536) ≤ ((3 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-671101233 / 21745664 : ℚ) : ℝ) - Real.exp ((-2688200867 / 86982656 : ℚ) : ℝ)) ≤ ((3 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_835 : sigmaPower (835 : Fin 1536) ≤ ((99109164901951 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_836 : sigmaFactor (836 : Fin 1536) ≤ ((3 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-670330727 / 21741568 : ℚ) : ℝ) - Real.exp ((-167819883 / 5435392 : ℚ) : ℝ)) ≤ ((3 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_836 : sigmaPower (836 : Fin 1536) ≤ ((98986427378779 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_837 : sigmaFactor (837 : Fin 1536) ≤ ((7 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-446373719 / 14491648 : ℚ) : ℝ) - Real.exp ((-894012273 / 28983296 : ℚ) : ℝ)) ≤ ((7 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_837 : sigmaPower (837 : Fin 1536) ≤ ((98863643600653 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_838 : sigmaFactor (838 : Fin 1536) ≤ ((7 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-1337581575 / 43466752 : ℚ) : ℝ) - Real.exp ((-669739235 / 21733376 : ℚ) : ℝ)) ≤ ((7 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_838 : sigmaPower (838 : Fin 1536) ≤ ((98740813541419 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_839 : sigmaFactor (839 : Fin 1536) ≤ ((7 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-334010677 / 10864640 : ℚ) : ℝ) - Real.exp ((-2675878491 / 86917120 : ℚ) : ℝ)) ≤ ((7 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_839 : sigmaPower (839 : Fin 1536) ≤ ((49308968587453 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_840 : sigmaFactor (840 : Fin 1536) ≤ ((7 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-6541689 / 212992 : ℚ) : ℝ) - Real.exp ((-818873 / 26624 : ℚ) : ℝ)) ≤ ((7 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_840 : sigmaPower (840 : Fin 1536) ≤ ((98495014474921 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_841 : sigmaFactor (841 : Fin 1536) ≤ ((7 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-1332967119 / 43442176 : ℚ) : ℝ) - Real.exp ((-2669725883 / 86884352 : ℚ) : ℝ)) ≤ ((7 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_841 : sigmaPower (841 : Fin 1536) ≤ ((98372045415253 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_842 : sigmaFactor (842 : Fin 1536) ≤ ((1 / 35184372088832 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-121039127 / 3948544 : ℚ) : ℝ) - Real.exp ((-60605721 / 1974272 : ℚ) : ℝ)) ≤ ((1 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_842 : sigmaPower (842 : Fin 1536) ≤ ((49124514984835 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_843 : sigmaFactor (843 : Fin 1536) ≤ ((1 / 35184372088832 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-221649065 / 7237632 : ℚ) : ℝ) - Real.exp ((-887859665 / 28950528 : ℚ) : ℝ)) ≤ ((1 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_843 : sigmaPower (843 : Fin 1536) ≤ ((98125968111921 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_844 : sigmaFactor (844 : Fin 1536) ≤ ((1 / 35184372088832 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-664179549 / 21708800 : ℚ) : ℝ) - Real.exp ((-166281731 / 5427200 : ℚ) : ℝ)) ≤ ((1 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_844 : sigmaPower (844 : Fin 1536) ≤ ((12250357476967 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_845 : sigmaFactor (845 : Fin 1536) ≤ ((1 / 35184372088832 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-1326824521 / 43409408 : ℚ) : ℝ) - Real.exp ((-2657437827 / 86818816 : ℚ) : ℝ)) ≤ ((1 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_845 : sigmaPower (845 : Fin 1536) ≤ ((97879705054823 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_846 : sigmaFactor (846 : Fin 1536) ≤ ((1 / 35184372088832 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-441763553 / 14467072 : ℚ) : ℝ) - Real.exp ((-221197449 / 7233536 : ℚ) : ℝ)) ≤ ((1 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_846 : sigmaPower (846 : Fin 1536) ≤ ((97756503802871 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_847 : sigmaFactor (847 : Fin 1536) ≤ ((9 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-165469689 / 5424128 : ℚ) : ℝ) - Real.exp ((-2651302379 / 86786048 : ℚ) : ℝ)) ≤ ((9 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_847 : sigmaPower (847 : Fin 1536) ≤ ((48816628016775 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_848 : sigmaFactor (848 : Fin 1536) ≤ ((9 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-165278135 / 5423104 : ℚ) : ℝ) - Real.exp ((-10344675 / 338944 : ℚ) : ℝ)) ≤ ((9 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_848 : sigmaPower (848 : Fin 1536) ≤ ((48754980860255 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_849 : sigmaFactor (849 : Fin 1536) ≤ ((9 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-440231121 / 14458880 : ℚ) : ℝ) - Real.exp ((-881724217 / 28917760 : ℚ) : ℝ)) ≤ ((9 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_849 : sigmaPower (849 : Fin 1536) ≤ ((97386620837379 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_850 : sigmaFactor (850 : Fin 1536) ≤ ((9 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-1319162361 / 43368448 : ℚ) : ℝ) - Real.exp ((-660527483 / 21684224 : ℚ) : ℝ)) ≤ ((9 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_850 : sigmaPower (850 : Fin 1536) ≤ ((97263233357769 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_851 : sigmaFactor (851 : Fin 1536) ≤ ((5 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-658816037 / 21680128 : ℚ) : ℝ) - Real.exp ((-2639048643 / 86720512 : ℚ) : ℝ)) ≤ ((5 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_851 : sigmaPower (851 : Fin 1536) ≤ ((24284949813817 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_852 : sigmaFactor (852 : Fin 1536) ≤ ((5 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-219350417 / 7225344 : ℚ) : ℝ) - Real.exp ((-54916433 / 1806336 : ℚ) : ℝ)) ≤ ((5 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_852 : sigmaPower (852 : Fin 1536) ≤ ((97016318503447 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_853 : sigmaFactor (853 : Fin 1536) ≤ ((5 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-119506695 / 3940352 : ℚ) : ℝ) - Real.exp ((-239357305 / 7880704 : ℚ) : ℝ)) ≤ ((5 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_853 : sigmaPower (853 : Fin 1536) ≤ ((48446395537927 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_854 : sigmaFactor (854 : Fin 1536) ≤ ((11 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-1313045503 / 43335680 : ℚ) : ℝ) - Real.exp ((-657468339 / 21667840 : ℚ) : ℝ)) ≤ ((11 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_854 : sigmaPower (854 : Fin 1536) ≤ ((96769216946021 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_855 : sigmaFactor (855 : Fin 1536) ≤ ((11 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-109293173 / 3610624 : ℚ) : ℝ) - Real.exp ((-875605929 / 28884992 : ℚ) : ℝ)) ≤ ((11 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_855 : sigmaPower (855 : Fin 1536) ≤ ((3020174877733 / 8796093022208 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_856 : sigmaFactor (856 : Fin 1536) ≤ ((11 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-327497841 / 10829824 : ℚ) : ℝ) - Real.exp ((-40996307 / 1353728 : ℚ) : ℝ)) ≤ ((11 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_856 : sigmaPower (856 : Fin 1536) ≤ ((48260964236825 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_857 : sigmaFactor (857 : Fin 1536) ≤ ((3 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-76968551 / 2547712 : ℚ) : ℝ) - Real.exp ((-154159467 / 5095424 : ℚ) : ℝ)) ≤ ((3 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_857 : sigmaPower (857 : Fin 1536) ≤ ((96398214078071 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_858 : sigmaFactor (858 : Fin 1536) ≤ ((3 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-435646695 / 14434304 : ℚ) : ℝ) - Real.exp ((-218138305 / 7217152 : ℚ) : ℝ)) ≤ ((3 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_858 : sigmaPower (858 : Fin 1536) ≤ ((96274452874171 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_859 : sigmaFactor (859 : Fin 1536) ≤ ((3 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-652707759 / 21647360 : ℚ) : ℝ) - Real.exp ((-2614609811 / 86589440 : ℚ) : ℝ)) ≤ ((3 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_859 : sigmaPower (859 : Fin 1536) ≤ ((48075322417689 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_860 : sigmaFactor (860 : Fin 1536) ≤ ((13 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-651945833 / 21643264 : ℚ) : ℝ) - Real.exp ((-163222587 / 5410816 : ℚ) : ℝ)) ≤ ((13 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_860 : sigmaPower (860 : Fin 1536) ≤ ((48013394967551 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_861 : sigmaFactor (861 : Fin 1536) ≤ ((13 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-434122843 / 14426112 : ℚ) : ℝ) - Real.exp ((-869504801 / 28852224 : ℚ) : ℝ)) ≤ ((13 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_861 : sigmaPower (861 : Fin 1536) ≤ ((23975722036683 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_862 : sigmaFactor (862 : Fin 1536) ≤ ((13 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-1300846107 / 43270144 : ℚ) : ℝ) - Real.exp ((-651367211 / 21635072 : ℚ) : ℝ)) ≤ ((13 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_862 : sigmaPower (862 : Fin 1536) ≤ ((95778939443637 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_863 : sigmaFactor (863 : Fin 1536) ≤ ((7 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-81207775 / 2703872 : ℚ) : ℝ) - Real.exp ((-2602424715 / 86523904 : ℚ) : ℝ)) ≤ ((7 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_863 : sigmaPower (863 : Fin 1536) ≤ ((47827471899583 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_864 : sigmaFactor (864 : Fin 1536) ≤ ((7 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-2457961 / 81920 : ℚ) : ℝ) - Real.exp ((-76923 / 2560 : ℚ) : ℝ)) ≤ ((7 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_864 : sigmaPower (864 : Fin 1536) ≤ ((95530901186647 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_865 : sigmaFactor (865 : Fin 1536) ≤ ((7 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-1296283131 / 43245568 : ℚ) : ℝ) - Real.exp ((-2596340747 / 86491136 : ℚ) : ℝ)) ≤ ((7 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_865 : sigmaPower (865 : Fin 1536) ≤ ((95406811579391 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_866 : sigmaFactor (866 : Fin 1536) ≤ ((15 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-1294763569 / 43237376 : ℚ) : ℝ) - Real.exp ((-648325227 / 21618688 : ℚ) : ℝ)) ≤ ((15 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_866 : sigmaPower (866 : Fin 1536) ≤ ((23820668737671 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_867 : sigmaFactor (867 : Fin 1536) ≤ ((15 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-215540787 / 7204864 : ℚ) : ℝ) - Real.exp ((-863420833 / 28819456 : ℚ) : ℝ)) ≤ ((15 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_867 : sigmaPower (867 : Fin 1536) ≤ ((47579245636897 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_868 : sigmaFactor (868 : Fin 1536) ≤ ((1 / 17592186044416 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-645863295 / 21610496 : ℚ) : ℝ) - Real.exp ((-161701595 / 5402624 : ℚ) : ℝ)) ≤ ((1 / 17592186044416 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_868 : sigmaPower (868 : Fin 1536) ≤ ((95034260521971 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_869 : sigmaFactor (869 : Fin 1536) ≤ ((1 / 17592186044416 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-1290209173 / 43212800 : ℚ) : ℝ) - Real.exp ((-2584189971 / 86425600 : ℚ) : ℝ)) ≤ ((1 / 17592186044416 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_869 : sigmaPower (869 : Fin 1536) ≤ ((11863747833555 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_870 : sigmaFactor (870 : Fin 1536) ≤ ((17 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-429564157 / 14401536 : ℚ) : ℝ) - Real.exp ((-215096321 / 7200768 : ℚ) : ℝ)) ≤ ((17 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_870 : sigmaPower (870 : Fin 1536) ≤ ((47392828843205 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_871 : sigmaFactor (871 : Fin 1536) ≤ ((17 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-321794121 / 10799104 : ℚ) : ℝ) - Real.exp ((-2578123163 / 86392832 : ℚ) : ℝ)) ≤ ((17 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_871 : sigmaPower (871 : Fin 1536) ≤ ((94661285549067 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_872 : sigmaFactor (872 : Fin 1536) ≤ ((9 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-321415303 / 10797056 : ℚ) : ℝ) - Real.exp ((-40235811 / 1349632 : ℚ) : ℝ)) ≤ ((9 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_872 : sigmaPower (872 : Fin 1536) ≤ ((47268433114789 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_873 : sigmaFactor (873 : Fin 1536) ≤ ((9 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-428048885 / 14393344 : ℚ) : ℝ) - Real.exp ((-857354025 / 28786688 : ℚ) : ℝ)) ≤ ((9 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_873 : sigmaPower (873 : Fin 1536) ≤ ((94412399701089 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_874 : sigmaFactor (874 : Fin 1536) ≤ ((19 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-75448989 / 2539520 : ℚ) : ℝ) - Real.exp ((-37779907 / 1269760 : ℚ) : ℝ)) ≤ ((19 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_874 : sigmaPower (874 : Fin 1536) ≤ ((47143942968363 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_875 : sigmaFactor (875 : Fin 1536) ≤ ((19 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-58232713 / 1961984 : ℚ) : ℝ) - Real.exp ((-233273337 / 7847936 : ℚ) : ℝ)) ≤ ((19 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_875 : sigmaPower (875 : Fin 1536) ≤ ((47081662454797 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_876 : sigmaFactor (876 : Fin 1536) ≤ ((5 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-213267879 / 7192576 : ℚ) : ℝ) - Real.exp ((-53395441 / 1798144 : ℚ) : ℝ)) ≤ ((5 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_876 : sigmaPower (876 : Fin 1536) ≤ ((94038716592779 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_877 : sigmaFactor (877 : Fin 1536) ≤ ((5 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-1278095577 / 43147264 : ℚ) : ℝ) - Real.exp ((-2559957059 / 86294528 : ℚ) : ℝ)) ≤ ((5 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_877 : sigmaPower (877 : Fin 1536) ≤ ((93914060959343 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_878 : sigmaFactor (878 : Fin 1536) ≤ ((21 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-1276584595 / 43139072 : ℚ) : ℝ) - Real.exp ((-639233595 / 21569536 : ℚ) : ℝ)) ≤ ((21 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_878 : sigmaPower (878 : Fin 1536) ≤ ((93789357982333 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_879 : sigmaFactor (879 : Fin 1536) ≤ ((11 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-53128097 / 1797120 : ℚ) : ℝ) - Real.exp ((-851304377 / 28753920 : ℚ) : ℝ)) ≤ ((11 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_879 : sigmaPower (879 : Fin 1536) ≤ ((93664607634771 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_880 : sigmaFactor (880 : Fin 1536) ≤ ((11 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-159195597 / 5390336 : ℚ) : ℝ) - Real.exp ((-9964427 / 336896 : ℚ) : ℝ)) ≤ ((11 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_880 : sigmaPower (880 : Fin 1536) ≤ ((93539809889661 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_881 : sigmaFactor (881 : Fin 1536) ≤ ((23 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-1272055939 / 43114496 : ℚ) : ℝ) - Real.exp ((-2547874923 / 86228992 : ℚ) : ℝ)) ≤ ((23 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_881 : sigmaPower (881 : Fin 1536) ≤ ((93414964719985 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_882 : sigmaFactor (882 : Fin 1536) ≤ ((3 / 35184372088832 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-423515939 / 14368768 : ℚ) : ℝ) - Real.exp ((-212071497 / 7184384 : ℚ) : ℝ)) ≤ ((3 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_882 : sigmaPower (882 : Fin 1536) ≤ ((93290072098705 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_883 : sigmaFactor (883 : Fin 1536) ≤ ((3 / 35184372088832 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-634520205 / 21549056 : ℚ) : ℝ) - Real.exp ((-2541842435 / 86196224 : ℚ) : ℝ)) ≤ ((3 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_883 : sigmaPower (883 : Fin 1536) ≤ ((93165131998763 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_884 : sigmaFactor (884 : Fin 1536) ≤ ((25 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-633766859 / 21544960 : ℚ) : ℝ) - Real.exp ((-158676771 / 5386240 : ℚ) : ℝ)) ≤ ((25 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_884 : sigmaPower (884 : Fin 1536) ≤ ((93040144393079 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_885 : sigmaFactor (885 : Fin 1536) ≤ ((13 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-422009247 / 14360576 : ℚ) : ℝ) - Real.exp ((-845271889 / 28721152 : ℚ) : ℝ)) ≤ ((13 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_885 : sigmaPower (885 : Fin 1536) ≤ ((46457554627277 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_886 : sigmaFactor (886 : Fin 1536) ≤ ((13 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-114956589 / 3915776 : ℚ) : ℝ) - Real.exp ((-57563737 / 1957888 : ℚ) : ℝ)) ≤ ((13 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_886 : sigmaPower (886 : Fin 1536) ≤ ((23197506639017 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_887 : sigmaFactor (887 : Fin 1536) ≤ ((27 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-315754483 / 10766336 : ℚ) : ℝ) - Real.exp ((-2529794619 / 86130688 : ℚ) : ℝ)) ≤ ((27 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_887 : sigmaPower (887 : Fin 1536) ≤ ((5791556016905 / 17592186044416 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_888 : sigmaFactor (888 : Fin 1536) ≤ ((7 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-105126175 / 3588096 : ℚ) : ℝ) - Real.exp ((-13160345 / 448512 : ℚ) : ℝ)) ≤ ((7 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_888 : sigmaPower (888 : Fin 1536) ≤ ((92539718370627 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_889 : sigmaFactor (889 : Fin 1536) ≤ ((29 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-1260010983 / 43048960 : ℚ) : ℝ) - Real.exp ((-2523779291 / 86097920 : ℚ) : ℝ)) ≤ ((29 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_889 : sigmaPower (889 : Fin 1536) ≤ ((5775905801833 / 17592186044416 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_890 : sigmaFactor (890 : Fin 1536) ≤ ((15 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-1258508581 / 43040768 : ℚ) : ℝ) - Real.exp ((-630193443 / 21520384 : ℚ) : ℝ)) ≤ ((15 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_890 : sigmaPower (890 : Fin 1536) ≤ ((92289219619381 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_891 : sigmaFactor (891 : Fin 1536) ≤ ((15 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-12323597 / 421888 : ℚ) : ℝ) - Real.exp ((-49368033 / 1687552 : ℚ) : ℝ)) ≤ ((15 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_891 : sigmaPower (891 : Fin 1536) ≤ ((11520487339195 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_892 : sigmaFactor (892 : Fin 1536) ≤ ((31 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-627752961 / 21512192 : ℚ) : ℝ) - Real.exp ((-157172939 / 5378048 : ℚ) : ℝ)) ≤ ((31 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_892 : sigmaPower (892 : Fin 1536) ≤ ((46019265042311 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_893 : sigmaFactor (893 : Fin 1536) ≤ ((1 / 8796093022208 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-1254005665 / 43016192 : ℚ) : ℝ) - Real.exp ((-2511765795 / 86032384 : ℚ) : ℝ)) ≤ ((1 / 8796093022208 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_893 : sigmaPower (893 : Fin 1536) ≤ ((45956556852651 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_894 : sigmaFactor (894 : Fin 1536) ≤ ((33 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-417502041 / 14336000 : ℚ) : ℝ) - Real.exp ((-209063833 / 7168000 : ℚ) : ℝ)) ≤ ((33 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_894 : sigmaPower (894 : Fin 1536) ≤ ((91787649548313 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_895 : sigmaFactor (895 : Fin 1536) ≤ ((17 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((1211 / 100 : ℚ) : ℝ) * (Real.exp ((-19546989 / 671872 : ℚ) : ℝ) - Real.exp ((-2505767627 / 85999616 : ℚ) : ℝ)) ≤ ((17 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_895 : sigmaPower (895 : Fin 1536) ≤ ((45831068793175 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

end LegendreK6.M2Pilot.Enclosures.Sigma006
