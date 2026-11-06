import LegendreK6.M3FarDefinitions
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp

/-! Generated proposals: every bound is checked by Lean, not by trusting Arb. -/
namespace LegendreK6.M3Far.Enclosures.Sigma001
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem sigma_factor_upper_32 : sigmaFactor (32 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-263305 / 3008 : ℚ) : ℝ) - Real.exp ((-8265 / 94 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_32 : sigmaPower (32 : Fin 384) ≤ ((175672325890339 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_33 : sigmaFactor (33 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-1399363 / 16032 : ℚ) : ℝ) - Real.exp ((-2811251 / 32064 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_33 : sigmaPower (33 : Fin 384) ≤ ((87644902927869 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_34 : sigmaFactor (34 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-4183323 / 48064 : ℚ) : ℝ) - Real.exp ((-2101049 / 24032 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_34 : sigmaPower (34 : Fin 384) ≤ ((174906776473555 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_35 : sigmaFactor (35 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-2084291 / 24016 : ℚ) : ℝ) - Real.exp ((-8374689 / 96064 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_35 : sigmaPower (35 : Fin 384) ≤ ((174523236725773 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_36 : sigmaFactor (36 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-692311 / 8000 : ℚ) : ℝ) - Real.exp ((-173859 / 2000 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_36 : sigmaPower (36 : Fin 384) ≤ ((43534796397915 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_37 : sigmaFactor (37 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-4139175 / 47968 : ℚ) : ℝ) - Real.exp ((-8315825 / 95936 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_37 : sigmaPower (37 : Fin 384) ≤ ((173754622047761 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_38 : sigmaFactor (38 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-4124509 / 47936 : ℚ) : ℝ) - Real.exp ((-2071617 / 23968 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_38 : sigmaPower (38 : Fin 384) ≤ ((86684772533945 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_39 : sigmaFactor (39 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-342489 / 3992 : ℚ) : ℝ) - Real.exp ((-2752387 / 31936 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_39 : sigmaPower (39 : Fin 384) ≤ ((43245988405779 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_40 : sigmaFactor (40 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-1023813 / 11968 : ℚ) : ℝ) - Real.exp ((-128561 / 1496 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_40 : sigmaPower (40 : Fin 384) ≤ ((172597846681757 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_41 : sigmaFactor (41 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-313897 / 3680 : ℚ) : ℝ) - Real.exp ((-630669 / 7360 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_41 : sigmaPower (41 : Fin 384) ≤ ((86105611604687 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_42 : sigmaFactor (42 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-1355365 / 15936 : ℚ) : ℝ) - Real.exp ((-680795 / 7968 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_42 : sigmaPower (42 : Fin 384) ≤ ((85912041084377 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_43 : sigmaFactor (43 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-2025777 / 23888 : ℚ) : ℝ) - Real.exp ((-8140433 / 95552 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_43 : sigmaPower (43 : Fin 384) ≤ ((171436422519909 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_44 : sigmaFactor (44 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-2018519 / 23872 : ℚ) : ℝ) - Real.exp ((-506961 / 5968 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_44 : sigmaPower (44 : Fin 384) ≤ ((42762060805015 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_45 : sigmaFactor (45 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-1340849 / 15904 : ℚ) : ℝ) - Real.exp ((-2694123 / 31808 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_45 : sigmaPower (45 : Fin 384) ≤ ((170659543223631 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_46 : sigmaFactor (46 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-4008081 / 47680 : ℚ) : ℝ) - Real.exp ((-2013353 / 23840 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_46 : sigmaPower (46 : Fin 384) ≤ ((170270321482241 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_47 : sigmaFactor (47 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-499205 / 5956 : ℚ) : ℝ) - Real.exp ((-8024505 / 95296 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_47 : sigmaPower (47 : Fin 384) ≤ ((84940288472345 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_48 : sigmaFactor (48 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-165801 / 1984 : ℚ) : ℝ) - Real.exp ((-10411 / 124 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_48 : sigmaPower (48 : Fin 384) ≤ ((169490308556955 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_49 : sigmaFactor (49 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-3964833 / 47584 : ℚ) : ℝ) - Real.exp ((-7966841 / 95168 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_49 : sigmaPower (49 : Fin 384) ≤ ((84549757631087 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_50 : sigmaFactor (50 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-3950467 / 47552 : ℚ) : ℝ) - Real.exp ((-1984521 / 23776 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_50 : sigmaPower (50 : Fin 384) ≤ ((168708196000645 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_51 : sigmaFactor (51 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-656021 / 7920 : ℚ) : ℝ) - Real.exp ((-2636459 / 31680 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_51 : sigmaPower (51 : Fin 384) ≤ ((168316349709807 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_52 : sigmaFactor (52 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-1960905 / 23744 : ℚ) : ℝ) - Real.exp ((-492545 / 5936 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_52 : sigmaPower (52 : Fin 384) ≤ ((167923975324237 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_53 : sigmaFactor (53 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-3907519 / 47456 : ℚ) : ℝ) - Real.exp ((-7852113 / 94912 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_53 : sigmaPower (53 : Fin 384) ≤ ((167531071775639 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_54 : sigmaFactor (54 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-99827 / 1216 : ℚ) : ℝ) - Real.exp ((-50151 / 608 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_54 : sigmaPower (54 : Fin 384) ≤ ((167137637992833 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_55 : sigmaFactor (55 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-969753 / 11848 : ℚ) : ℝ) - Real.exp ((-7795049 / 94784 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_55 : sigmaPower (55 : Fin 384) ≤ ((10421479556359 / 17592186044416 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_56 : sigmaFactor (56 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-966199 / 11840 : ℚ) : ℝ) - Real.exp ((-121353 / 1480 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_56 : sigmaPower (56 : Fin 384) ≤ ((166349175425397 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_57 : sigmaFactor (57 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-1283535 / 15776 : ℚ) : ℝ) - Real.exp ((-2579395 / 31552 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_57 : sigmaPower (57 : Fin 384) ≤ ((165954144483903 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_58 : sigmaFactor (58 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-3836439 / 47296 : ℚ) : ℝ) - Real.exp ((-1927457 / 23648 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_58 : sigmaPower (58 : Fin 384) ≤ ((82779289497225 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_59 : sigmaFactor (59 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-1911149 / 23632 : ℚ) : ℝ) - Real.exp ((-7681521 / 94528 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_59 : sigmaPower (59 : Fin 384) ≤ ((165162477871295 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_60 : sigmaFactor (60 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-634697 / 7872 : ℚ) : ℝ) - Real.exp ((-159443 / 1968 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_60 : sigmaPower (60 : Fin 384) ≤ ((82382920012875 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_61 : sigmaFactor (61 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-3794091 / 47200 : ℚ) : ℝ) - Real.exp ((-7625057 / 94400 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_61 : sigmaPower (61 : Fin 384) ≤ ((82184332183089 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_62 : sigmaFactor (62 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-3780025 / 47168 : ℚ) : ℝ) - Real.exp ((-1899225 / 23584 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_62 : sigmaPower (62 : Fin 384) ≤ ((20496368724747 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_63 : sigmaFactor (63 : Fin 384) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((3023 / 500 : ℚ) : ℝ) * (Real.exp ((-39229 / 491 : ℚ) : ℝ) - Real.exp ((-2522931 / 31424 : ℚ) : ℝ)) ≤ ((1 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_63 : sigmaPower (63 : Fin 384) ≤ ((40893173805893 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

end LegendreK6.M3Far.Enclosures.Sigma001
