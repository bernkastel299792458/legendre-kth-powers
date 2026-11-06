import LegendreK6.M2PilotDefinitions
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp

/-! Generated proposals: every bound is checked by Lean, not by trusting Arb. -/
namespace LegendreK6.M2Pilot.Enclosures.Sigma008
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem sigma_factor_upper_1024 : sigmaFactor (1024 : Fin 1536) ≤ ((1789 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-2077449 / 81920 : ℚ) : ℝ) - Real.exp ((-8129 / 320 : ℚ) : ℝ)) ≤ ((1789 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1024 : sigmaPower (1024 : Fin 1536) ≤ ((75059993789509 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1025 : sigmaFactor (1025 : Fin 1536) ≤ ((1841 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-1062248011 / 41934848 : ℚ) : ℝ) - Real.exp ((-2128156107 / 83869696 : ℚ) : ℝ)) ≤ ((1841 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1025 : sigmaPower (1025 : Fin 1536) ≤ ((37464013309669 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1026 : sigmaFactor (1026 : Fin 1536) ≤ ((947 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-353614283 / 13975552 : ℚ) : ℝ) - Real.exp ((-177112089 / 6987776 : ℚ) : ℝ)) ≤ ((947 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1026 : sigmaPower (1026 : Fin 1536) ≤ ((37398003939673 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1027 : sigmaFactor (1027 : Fin 1536) ≤ ((1949 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-31159953 / 1232896 : ℚ) : ℝ) - Real.exp ((-124855027 / 4931584 : ℚ) : ℝ)) ≤ ((1949 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1027 : sigmaPower (1027 : Fin 1536) ≤ ((18665984384825 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1028 : sigmaFactor (1028 : Fin 1536) ≤ ((1003 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-529017335 / 20955136 : ℚ) : ℝ) - Real.exp ((-132482955 / 5238784 : ℚ) : ℝ)) ≤ ((1003 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1028 : sigmaPower (1028 : Fin 1536) ≤ ((74531815568941 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1029 : sigmaFactor (1029 : Fin 1536) ≤ ((129 / 17592186044416 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-32019141 / 1269760 : ℚ) : ℝ) - Real.exp ((-64149107 / 2539520 : ℚ) : ℝ)) ≤ ((129 / 17592186044416 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1029 : sigmaPower (1029 : Fin 1536) ≤ ((18599910484497 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1030 : sigmaFactor (1030 : Fin 1536) ≤ ((2123 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-1055229351 / 41893888 : ℚ) : ℝ) - Real.exp ((-528528803 / 20946944 : ℚ) : ℝ)) ≤ ((2123 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1030 : sigmaPower (1030 : Fin 1536) ≤ ((74267416616135 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1031 : sigmaFactor (1031 : Fin 1536) ≤ ((2185 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-263456941 / 10471424 : ℚ) : ℝ) - Real.exp ((-2111311323 / 83771392 : ℚ) : ℝ)) ≤ ((2185 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1031 : sigmaPower (1031 : Fin 1536) ≤ ((74135139573053 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1032 : sigmaFactor (1032 : Fin 1536) ≤ ((281 / 35184372088832 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-87702241 / 3489792 : ℚ) : ℝ) - Real.exp ((-10981817 / 436224 : ℚ) : ℝ)) ≤ ((281 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1032 : sigmaPower (1032 : Fin 1536) ≤ ((74002810778389 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1033 : sigmaFactor (1033 : Fin 1536) ≤ ((2313 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-1051026735 / 41869312 : ℚ) : ℝ) - Real.exp ((-2105707835 / 83738624 : ℚ) : ℝ)) ≤ ((2313 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1033 : sigmaPower (1033 : Fin 1536) ≤ ((73870430201767 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1034 : sigmaFactor (1034 : Fin 1536) ≤ ((595 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-1049627293 / 41861120 : ℚ) : ℝ) - Real.exp ((-525727059 / 20930560 : ℚ) : ℝ)) ≤ ((595 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1034 : sigmaPower (1034 : Fin 1536) ≤ ((36868998906393 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1035 : sigmaFactor (1035 : Fin 1536) ≤ ((2449 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-174704761 / 6975488 : ℚ) : ℝ) - Real.exp ((-700036689 / 27901952 : ℚ) : ℝ)) ≤ ((2449 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1035 : sigmaPower (1035 : Fin 1536) ≤ ((36802756790511 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1036 : sigmaFactor (1036 : Fin 1536) ≤ ((315 / 35184372088832 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-523415277 / 20922368 : ℚ) : ℝ) - Real.exp ((-131082083 / 5230592 : ℚ) : ℝ)) ≤ ((315 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1036 : sigmaPower (1036 : Fin 1536) ≤ ((73472977476027 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1037 : sigmaFactor (1037 : Fin 1536) ≤ ((81 / 8796093022208 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-1045433257 / 41836544 : ℚ) : ℝ) - Real.exp ((-2094518019 / 83673088 : ℚ) : ℝ)) ≤ ((81 / 8796093022208 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1037 : sigmaPower (1037 : Fin 1536) ≤ ((73340389467329 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1038 : sigmaFactor (1038 : Fin 1536) ≤ ((2667 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-348012225 / 13942784 : ℚ) : ℝ) - Real.exp ((-174310345 / 6971392 : ℚ) : ℝ)) ≤ ((2667 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1038 : sigmaPower (1038 : Fin 1536) ≤ ((73207749524433 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1039 : sigmaFactor (1039 : Fin 1536) ≤ ((343 / 35184372088832 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-130330101 / 5227520 : ℚ) : ℝ) - Real.exp ((-2088931691 / 83640320 : ℚ) : ℝ)) ≤ ((343 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1039 : sigmaPower (1039 : Fin 1536) ≤ ((73075057616819 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1040 : sigmaFactor (1040 : Fin 1536) ≤ ((353 / 35184372088832 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-11832337 / 475136 : ℚ) : ℝ) - Real.exp ((-740817 / 29696 : ℚ) : ℝ)) ≤ ((353 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1040 : sigmaPower (1040 : Fin 1536) ≤ ((72942313713943 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1041 : sigmaFactor (1041 : Fin 1536) ≤ ((2905 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-346617073 / 13934592 : ℚ) : ℝ) - Real.exp ((-694450361 / 27869184 : ℚ) : ℝ)) ≤ ((2905 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1041 : sigmaPower (1041 : Fin 1536) ≤ ((36404758892619 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1042 : sigmaFactor (1042 : Fin 1536) ≤ ((2989 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-1038457497 / 41795584 : ℚ) : ℝ) - Real.exp ((-520140731 / 20897792 : ℚ) : ℝ)) ≤ ((2989 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1042 : sigmaPower (1042 : Fin 1536) ≤ ((4542291862507 / 17592186044416 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1043 : sigmaFactor (1043 : Fin 1536) ≤ ((3075 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-518532245 / 20893696 : ℚ) : ℝ) - Real.exp ((-2077776195 / 83574784 : ℚ) : ℝ)) ≤ ((3075 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1043 : sigmaPower (1043 : Fin 1536) ≤ ((72543769727951 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1044 : sigmaFactor (1044 : Fin 1536) ≤ ((791 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-10153649 / 409600 : ℚ) : ℝ) - Real.exp ((-2542881 / 102400 : ℚ) : ℝ)) ≤ ((791 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1044 : sigmaPower (1044 : Fin 1536) ≤ ((36205408769057 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1045 : sigmaFactor (1045 : Fin 1536) ≤ ((3255 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-1034280621 / 41771008 : ℚ) : ℝ) - Real.exp ((-2072207027 / 83542016 : ℚ) : ℝ)) ≤ ((3255 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1045 : sigmaPower (1045 : Fin 1536) ≤ ((72277813199939 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1046 : sigmaFactor (1046 : Fin 1536) ≤ ((3349 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-1032889759 / 41762816 : ℚ) : ℝ) - Real.exp ((-517356147 / 20881408 : ℚ) : ℝ)) ≤ ((3349 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1046 : sigmaPower (1046 : Fin 1536) ≤ ((72144756682737 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1047 : sigmaFactor (1047 : Fin 1536) ≤ ((1723 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-85958301 / 3479552 : ℚ) : ℝ) - Real.exp ((-688881193 / 27836416 : ℚ) : ℝ)) ≤ ((1723 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1047 : sigmaPower (1047 : Fin 1536) ≤ ((72011647955797 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1048 : sigmaFactor (1048 : Fin 1536) ≤ ((3545 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-257527545 / 10436608 : ℚ) : ℝ) - Real.exp ((-32247875 / 1304576 : ℚ) : ℝ)) ≤ ((3545 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1048 : sigmaPower (1048 : Fin 1536) ≤ ((2246202718387 / 8796093022208 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1049 : sigmaFactor (1049 : Fin 1536) ≤ ((57 / 4398046511104 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-1028721463 / 41738240 : ℚ) : ℝ) - Real.exp ((-2061085851 / 83476480 : ℚ) : ℝ)) ≤ ((57 / 4398046511104 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1049 : sigmaPower (1049 : Fin 1536) ≤ ((71745273749737 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1050 : sigmaFactor (1050 : Fin 1536) ≤ ((3753 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-342444487 / 13910016 : ℚ) : ℝ) - Real.exp ((-171525761 / 6955008 : ℚ) : ℝ)) ≤ ((3753 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1050 : sigmaPower (1050 : Fin 1536) ≤ ((4475750513067 / 17592186044416 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1051 : sigmaFactor (1051 : Fin 1536) ≤ ((3861 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-46633917 / 1896448 : ℚ) : ℝ) - Real.exp ((-186866713 / 7585792 : ℚ) : ℝ)) ≤ ((3861 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1051 : sigmaPower (1051 : Fin 1536) ≤ ((35739345167791 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1052 : sigmaFactor (1052 : Fin 1536) ≤ ((993 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-512279801 / 20856832 : ℚ) : ℝ) - Real.exp ((-128297499 / 5214208 : ℚ) : ℝ)) ≤ ((993 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1052 : sigmaPower (1052 : Fin 1536) ≤ ((71345320098433 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1053 : sigmaFactor (1053 : Fin 1536) ≤ ((4087 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-341057915 / 13901824 : ℚ) : ℝ) - Real.exp ((-683329185 / 27803648 : ℚ) : ℝ)) ≤ ((4087 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1053 : sigmaPower (1053 : Fin 1536) ≤ ((35605948733385 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1054 : sigmaFactor (1054 : Fin 1536) ≤ ((1051 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-1021788603 / 41697280 : ℚ) : ℝ) - Real.exp ((-511804139 / 20848640 : ℚ) : ℝ)) ≤ ((1051 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1054 : sigmaPower (1054 : Fin 1536) ≤ ((4442401400607 / 17592186044416 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1055 : sigmaFactor (1055 : Fin 1536) ≤ ((4325 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-63775261 / 2605568 : ℚ) : ℝ) - Real.exp ((-2044446987 / 83378176 : ℚ) : ℝ)) ≤ ((4325 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1055 : sigmaPower (1055 : Fin 1536) ≤ ((2217027965511 / 8796093022208 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1056 : sigmaFactor (1056 : Fin 1536) ≤ ((2225 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-21229593 / 868352 : ℚ) : ℝ) - Real.exp ((-664609 / 27136 : ℚ) : ℝ)) ≤ ((2225 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1056 : sigmaPower (1056 : Fin 1536) ≤ ((70811314895763 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1057 : sigmaFactor (1057 : Fin 1536) ≤ ((2289 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-1017637467 / 41672704 : ℚ) : ℝ) - Real.exp ((-2038912139 / 83345408 : ℚ) : ℝ)) ≤ ((2289 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1057 : sigmaPower (1057 : Fin 1536) ≤ ((35338841188495 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1058 : sigmaFactor (1058 : Fin 1536) ≤ ((2355 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-1016255185 / 41664512 : ℚ) : ℝ) - Real.exp ((-509036715 / 20832256 : ℚ) : ℝ)) ≤ ((2355 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1058 : sigmaPower (1058 : Fin 1536) ≤ ((70543997309055 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1059 : sigmaFactor (1059 : Fin 1536) ≤ ((4845 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-169145603 / 6942720 : ℚ) : ℝ) - Real.exp ((-677794337 / 27770880 : ℚ) : ℝ)) ≤ ((4845 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1059 : sigmaPower (1059 : Fin 1536) ≤ ((70410259660955 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1060 : sigmaFactor (1060 : Fin 1536) ≤ ((4985 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-506746383 / 20824064 : ℚ) : ℝ) - Real.exp ((-126913787 / 5206016 : ℚ) : ℝ)) ≤ ((4985 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1060 : sigmaPower (1060 : Fin 1536) ≤ ((1098069834401 / 4398046511104 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1061 : sigmaFactor (1061 : Fin 1536) ≤ ((641 / 35184372088832 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-59536037 / 2449408 : ℚ) : ℝ) - Real.exp ((-119285859 / 4898816 : ℚ) : ℝ)) ≤ ((641 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1061 : sigmaPower (1061 : Fin 1536) ≤ ((70142626500131 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1062 : sigmaFactor (1062 : Fin 1536) ≤ ((5275 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-2784389 / 114688 : ℚ) : ℝ) - Real.exp ((-1394697 / 57344 : ℚ) : ℝ)) ≤ ((5275 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1062 : sigmaPower (1062 : Fin 1536) ≤ ((2187772841415 / 8796093022208 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1063 : sigmaFactor (1063 : Fin 1536) ≤ ((5427 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-252338625 / 10405888 : ℚ) : ℝ) - Real.exp ((-2022341915 / 83247104 : ℚ) : ℝ)) ≤ ((5427 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1063 : sigmaPower (1063 : Fin 1536) ≤ ((34937391323005 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1064 : sigmaFactor (1064 : Fin 1536) ≤ ((5583 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-251994127 / 10403840 : ℚ) : ℝ) - Real.exp ((-31556019 / 1300480 : ℚ) : ℝ)) ≤ ((5583 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1064 : sigmaPower (1064 : Fin 1536) ≤ ((69740781631197 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1065 : sigmaFactor (1065 : Fin 1536) ≤ ((5743 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-335533077 / 13869056 : ℚ) : ℝ) - Real.exp ((-672276649 / 27738112 : ℚ) : ℝ)) ≤ ((5743 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1065 : sigmaPower (1065 : Fin 1536) ≤ ((17401681962423 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1066 : sigmaFactor (1066 : Fin 1536) ≤ ((1477 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-1005222669 / 41598976 : ℚ) : ℝ) - Real.exp ((-503519027 / 20799488 : ℚ) : ℝ)) ≤ ((1477 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1066 : sigmaPower (1066 : Fin 1536) ≤ ((69472621270321 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1067 : sigmaFactor (1067 : Fin 1536) ≤ ((3039 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-501923411 / 20795392 : ℚ) : ℝ) - Real.exp ((-2011323699 / 83181568 : ℚ) : ℝ)) ≤ ((3039 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1067 : sigmaPower (1067 : Fin 1536) ≤ ((34669230930943 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1068 : sigmaFactor (1068 : Fin 1536) ≤ ((6253 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-167078615 / 6930432 : ℚ) : ℝ) - Real.exp ((-41845265 / 1732608 : ℚ) : ℝ)) ≤ ((6253 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1068 : sigmaPower (1068 : Fin 1536) ≤ ((17301062398291 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1069 : sigmaFactor (1069 : Fin 1536) ≤ ((201 / 8796093022208 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-1001097273 / 41574400 : ℚ) : ℝ) - Real.exp ((-2005823171 / 83148800 : ℚ) : ℝ)) ≤ ((201 / 8796093022208 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1069 : sigmaPower (1069 : Fin 1536) ≤ ((17267496108227 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1070 : sigmaFactor (1070 : Fin 1536) ≤ ((6617 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-999723571 / 41566208 : ℚ) : ℝ) - Real.exp ((-500768763 / 20783104 : ℚ) : ℝ)) ≤ ((6617 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1070 : sigmaPower (1070 : Fin 1536) ≤ ((68935666349845 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1071 : sigmaFactor (1071 : Fin 1536) ≤ ((6807 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-41597941 / 1731584 : ℚ) : ℝ) - Real.exp ((-666776121 / 27705344 : ℚ) : ℝ)) ≤ ((6807 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1071 : sigmaPower (1071 : Fin 1536) ≤ ((34400647656339 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1072 : sigmaFactor (1072 : Fin 1536) ≤ ((3501 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-124622289 / 5193728 : ℚ) : ℝ) - Real.exp ((-7803059 / 324608 : ℚ) : ℝ)) ≤ ((3501 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1072 : sigmaPower (1072 : Fin 1536) ≤ ((68666871290087 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1073 : sigmaFactor (1073 : Fin 1536) ≤ ((7203 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-90509705 / 3776512 : ℚ) : ℝ) - Real.exp ((-181349025 / 7553024 : ℚ) : ℝ)) ≤ ((7203 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1073 : sigmaPower (1073 : Fin 1536) ≤ ((68532394250725 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1074 : sigmaFactor (1074 : Fin 1536) ≤ ((3705 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-331411971 / 13844480 : ℚ) : ℝ) - Real.exp ((-166008073 / 6922240 : ℚ) : ℝ)) ≤ ((3705 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1074 : sigmaPower (1074 : Fin 1536) ≤ ((68397864163221 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1075 : sigmaFactor (1075 : Fin 1536) ≤ ((3811 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-496432893 / 20762624 : ℚ) : ℝ) - Real.exp ((-1989355907 / 83050496 : ℚ) : ℝ)) ≤ ((3811 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1075 : sigmaPower (1075 : Fin 1536) ≤ ((17065820249045 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1076 : sigmaFactor (1076 : Fin 1536) ≤ ((7841 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-495748187 / 20758528 : ℚ) : ℝ) - Real.exp ((-124163523 / 5189632 : ℚ) : ℝ)) ≤ ((7841 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1076 : sigmaPower (1076 : Fin 1536) ≤ ((68128644718181 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1077 : sigmaFactor (1077 : Fin 1536) ≤ ((8065 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-330042559 / 13836288 : ℚ) : ℝ) - Real.exp ((-661292753 / 27672576 : ℚ) : ℝ)) ≤ ((8065 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1077 : sigmaPower (1077 : Fin 1536) ≤ ((67993955297779 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1078 : sigmaFactor (1078 : Fin 1536) ≤ ((1037 / 35184372088832 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-58162335 / 2441216 : ℚ) : ℝ) - Real.exp ((-29134435 / 1220608 : ℚ) : ℝ)) ≤ ((1037 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1078 : sigmaPower (1078 : Fin 1536) ≤ ((4241200793969 / 17592186044416 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1079 : sigmaFactor (1079 : Fin 1536) ≤ ((4267 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-246848107 / 10373120 : ℚ) : ℝ) - Real.exp ((-1978406331 / 82984960 : ℚ) : ℝ)) ≤ ((4267 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1079 : sigmaPower (1079 : Fin 1536) ≤ ((67724416903861 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1080 : sigmaFactor (1080 : Fin 1536) ≤ ((4389 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-82168823 / 3457024 : ℚ) : ℝ) - Real.exp ((-10289961 / 432128 : ℚ) : ℝ)) ≤ ((4389 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1080 : sigmaPower (1080 : Fin 1536) ≤ ((33794783933665 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1081 : sigmaFactor (1081 : Fin 1536) ≤ ((4515 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-984660039 / 41476096 : ℚ) : ℝ) - Real.exp ((-1972940123 / 82952192 : ℚ) : ℝ)) ≤ ((4515 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1081 : sigmaPower (1081 : Fin 1536) ≤ ((67454665562367 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1082 : sigmaFactor (1082 : Fin 1536) ≤ ((1161 / 35184372088832 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-983294917 / 41467904 : ℚ) : ℝ) - Real.exp ((-492552291 / 20733952 : ℚ) : ℝ)) ≤ ((1161 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1082 : sigmaPower (1082 : Fin 1536) ≤ ((33659854978701 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1083 : sigmaFactor (1083 : Fin 1536) ≤ ((4777 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-163655085 / 6909952 : ℚ) : ℝ) - Real.exp ((-655826545 / 27639808 : ℚ) : ℝ)) ≤ ((4777 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1083 : sigmaPower (1083 : Fin 1536) ≤ ((67184701020841 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1084 : sigmaFactor (1084 : Fin 1536) ≤ ((2457 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-44571219 / 1884160 : ℚ) : ℝ) - Real.exp ((-11163361 / 471040 : ℚ) : ℝ)) ≤ ((2457 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1084 : sigmaPower (1084 : Fin 1536) ≤ ((67049638721063 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1085 : sigmaFactor (1085 : Fin 1536) ≤ ((10109 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-979203841 / 41443328 : ℚ) : ℝ) - Real.exp ((-1962024867 / 82886656 : ℚ) : ℝ)) ≤ ((10109 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1085 : sigmaPower (1085 : Fin 1536) ≤ ((66914523026425 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1086 : sigmaFactor (1086 : Fin 1536) ≤ ((5199 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-325947193 / 13811712 : ℚ) : ℝ) - Real.exp ((-163274969 / 6905856 : ℚ) : ℝ)) ≤ ((5199 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1086 : sigmaPower (1086 : Fin 1536) ≤ ((66779353905257 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1087 : sigmaFactor (1087 : Fin 1536) ≤ ((10695 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-30515001 / 1294592 : ℚ) : ℝ) - Real.exp ((-1956575819 / 82853888 : ℚ) : ℝ)) ≤ ((10695 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1087 : sigmaPower (1087 : Fin 1536) ≤ ((8330516415733 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1088 : sigmaFactor (1088 : Fin 1536) ≤ ((11001 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-30472475 / 1294336 : ℚ) : ℝ) - Real.exp ((-477015 / 20224 : ℚ) : ℝ)) ≤ ((11001 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1088 : sigmaPower (1088 : Fin 1536) ≤ ((66508855256527 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1089 : sigmaFactor (1089 : Fin 1536) ≤ ((2829 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-324586361 / 13803520 : ℚ) : ℝ) - Real.exp ((-650377497 / 27607040 : ℚ) : ℝ)) ≤ ((2829 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1089 : sigmaPower (1089 : Fin 1536) ≤ ((16593381416375 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1090 : sigmaFactor (1090 : Fin 1536) ≤ ((11639 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-972399681 / 41402368 : ℚ) : ℝ) - Real.exp ((-487103243 / 20701184 : ℚ) : ℝ)) ≤ ((11639 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1090 : sigmaPower (1090 : Fin 1536) ≤ ((66238142521015 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1091 : sigmaFactor (1091 : Fin 1536) ≤ ((2993 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-485520497 / 20697088 : ℚ) : ℝ) - Real.exp ((-1945694883 / 82788352 : ℚ) : ℝ)) ≤ ((2993 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1091 : sigmaPower (1091 : Fin 1536) ≤ ((66102705791275 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1092 : sigmaFactor (1092 : Fin 1536) ≤ ((6157 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-161613837 / 6897664 : ℚ) : ℝ) - Real.exp ((-40478713 / 1724416 : ℚ) : ℝ)) ≤ ((6157 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1092 : sigmaPower (1092 : Fin 1536) ≤ ((65967215444461 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1093 : sigmaFactor (1093 : Fin 1536) ≤ ((12665 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-968325765 / 41377792 : ℚ) : ℝ) - Real.exp ((-1940262995 / 82755584 : ℚ) : ℝ)) ≤ ((12665 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1093 : sigmaPower (1093 : Fin 1536) ≤ ((8228958931091 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1094 : sigmaFactor (1094 : Fin 1536) ≤ ((13027 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-966969223 / 41369600 : ℚ) : ℝ) - Real.exp ((-484387299 / 20684800 : ℚ) : ℝ)) ≤ ((13027 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1094 : sigmaPower (1094 : Fin 1536) ≤ ((16424018443051 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1095 : sigmaFactor (1095 : Fin 1536) ≤ ((13399 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-430309 / 18432 : ℚ) : ℝ) - Real.exp ((-3448907 / 147456 : ℚ) : ℝ)) ≤ ((13399 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1095 : sigmaPower (1095 : Fin 1536) ≤ ((65560422382993 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1096 : sigmaFactor (1096 : Fin 1536) ≤ ((6891 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-241064571 / 10338304 : ℚ) : ℝ) - Real.exp ((-30189467 / 1292288 : ℚ) : ℝ)) ≤ ((6891 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1096 : sigmaPower (1096 : Fin 1536) ≤ ((8178089656147 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1097 : sigmaFactor (1097 : Fin 1536) ≤ ((14175 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-962903887 / 41345024 : ℚ) : ℝ) - Real.exp ((-1929416379 / 82690048 : ℚ) : ℝ)) ≤ ((14175 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1097 : sigmaPower (1097 : Fin 1536) ≤ ((16322239584701 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1098 : sigmaFactor (1098 : Fin 1536) ≤ ((14579 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-320516735 / 13778944 : ℚ) : ℝ) - Real.exp ((-160559025 / 6889472 : ℚ) : ℝ)) ≤ ((14579 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1098 : sigmaPower (1098 : Fin 1536) ≤ ((65153145619907 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1099 : sigmaFactor (1099 : Fin 1536) ≤ ((14995 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-480098619 / 20664320 : ℚ) : ℝ) - Real.exp ((-1924001651 / 82657280 : ℚ) : ℝ)) ≤ ((14995 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1099 : sigmaPower (1099 : Fin 1536) ≤ ((32508639530243 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1100 : sigmaFactor (1100 : Fin 1536) ≤ ((15423 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-479422493 / 20660224 : ℚ) : ℝ) - Real.exp ((-120081027 / 5165056 : ℚ) : ℝ)) ≤ ((15423 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1100 : sigmaPower (1100 : Fin 1536) ≤ ((64881358628521 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1101 : sigmaFactor (1101 : Fin 1536) ≤ ((7931 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-319164483 / 13770752 : ℚ) : ℝ) - Real.exp ((-639530881 / 27541504 : ℚ) : ℝ)) ≤ ((7931 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1101 : sigmaPower (1101 : Fin 1536) ≤ ((32372692145981 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1102 : sigmaFactor (1102 : Fin 1536) ≤ ((16315 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-956142627 / 41304064 : ℚ) : ℝ) - Real.exp ((-478972571 / 20652032 : ℚ) : ℝ)) ≤ ((16315 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1102 : sigmaPower (1102 : Fin 1536) ≤ ((4038084751171 / 17592186044416 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1103 : sigmaFactor (1103 : Fin 1536) ≤ ((4195 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-119349065 / 5161984 : ℚ) : ℝ) - Real.exp ((-1913189355 / 82591744 : ℚ) : ℝ)) ≤ ((4195 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1103 : sigmaPower (1103 : Fin 1536) ≤ ((64473273776745 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1104 : sigmaFactor (1104 : Fin 1536) ≤ ((8629 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-39726797 / 1720320 : ℚ) : ℝ) - Real.exp ((-2487617 / 107520 : ℚ) : ℝ)) ≤ ((8629 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1104 : sigmaPower (1104 : Fin 1536) ≤ ((64337137533865 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1105 : sigmaFactor (1105 : Fin 1536) ≤ ((17749 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-952094451 / 41279488 : ℚ) : ℝ) - Real.exp ((-1907791787 / 82558976 : ℚ) : ℝ)) ≤ ((17749 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1105 : sigmaPower (1105 : Fin 1536) ≤ ((64200947257945 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1106 : sigmaFactor (1106 : Fin 1536) ≤ ((18255 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-86431499 / 3751936 : ℚ) : ℝ) - Real.exp ((-43297617 / 1875968 : ℚ) : ℝ)) ≤ ((18255 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1106 : sigmaPower (1106 : Fin 1536) ≤ ((32032351458405 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1107 : sigmaFactor (1107 : Fin 1536) ≤ ((18775 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-158233207 / 6877184 : ℚ) : ℝ) - Real.exp ((-634133313 / 27508736 : ℚ) : ℝ)) ≤ ((18775 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1107 : sigmaPower (1107 : Fin 1536) ≤ ((63928404478259 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1108 : sigmaFactor (1108 : Fin 1536) ≤ ((19309 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-474026355 / 20627456 : ℚ) : ℝ) - Real.exp ((-118731635 / 5156864 : ℚ) : ℝ)) ≤ ((19309 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1108 : sigmaPower (1108 : Fin 1536) ≤ ((63792051910067 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1109 : sigmaFactor (1109 : Fin 1536) ≤ ((19859 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-946706893 / 41246720 : ℚ) : ℝ) - Real.exp ((-1897013811 / 82493440 : ℚ) : ℝ)) ≤ ((19859 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1109 : sigmaPower (1109 : Fin 1536) ≤ ((63655645179981 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1110 : sigmaFactor (1110 : Fin 1536) ≤ ((2553 / 35184372088832 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-315120597 / 13746176 : ℚ) : ℝ) - Real.exp ((-157860241 / 6873088 : ℚ) : ℝ)) ≤ ((2553 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1110 : sigmaPower (1110 : Fin 1536) ≤ ((63519184255723 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1111 : sigmaFactor (1111 : Fin 1536) ≤ ((21005 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-236004351 / 10307584 : ℚ) : ℝ) - Real.exp ((-1891633403 / 82460672 : ℚ) : ℝ)) ≤ ((21005 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1111 : sigmaPower (1111 : Fin 1536) ≤ ((31691334552495 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1112 : sigmaFactor (1112 : Fin 1536) ≤ ((10801 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-13862849 / 606208 : ℚ) : ℝ) - Real.exp ((-1736163 / 75776 : ℚ) : ℝ)) ≤ ((10801 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1112 : sigmaPower (1112 : Fin 1536) ≤ ((63246099695453 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1113 : sigmaFactor (1113 : Fin 1536) ≤ ((2777 / 35184372088832 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-313776925 / 13737984 : ℚ) : ℝ) - Real.exp ((-628752905 / 27475968 : ℚ) : ℝ)) ≤ ((2777 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1113 : sigmaPower (1113 : Fin 1536) ≤ ((63109475994757 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1114 : sigmaFactor (1114 : Fin 1536) ≤ ((357 / 4398046511104 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-939988533 / 41205760 : ℚ) : ℝ) - Real.exp ((-470893379 / 20602880 : ℚ) : ℝ)) ≤ ((357 / 4398046511104 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1114 : sigmaPower (1114 : Fin 1536) ≤ ((31486398985261 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1115 : sigmaFactor (1115 : Fin 1536) ≤ ((23497 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-469323503 / 20598784 : ℚ) : ℝ) - Real.exp ((-1880889747 / 82395136 : ℚ) : ℝ)) ≤ ((23497 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1115 : sigmaPower (1115 : Fin 1536) ≤ ((31418032795171 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1116 : sigmaFactor (1116 : Fin 1536) ≤ ((24165 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-156217699 / 6864896 : ℚ) : ℝ) - Real.exp ((-39129321 / 1716224 : ℚ) : ℝ)) ≤ ((24165 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1116 : sigmaPower (1116 : Fin 1536) ≤ ((62699278821785 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1117 : sigmaFactor (1117 : Fin 1536) ≤ ((6213 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-85087827 / 3743744 : ℚ) : ℝ) - Real.exp ((-170502409 / 7487488 : ℚ) : ℝ)) ≤ ((6213 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1117 : sigmaPower (1117 : Fin 1536) ≤ ((31281218816197 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1118 : sigmaFactor (1118 : Fin 1536) ≤ ((25557 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-934626715 / 41172992 : ℚ) : ℝ) - Real.exp ((-468211755 / 20586496 : ℚ) : ℝ)) ≤ ((25557 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1118 : sigmaPower (1118 : Fin 1536) ≤ ((62425541989683 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1119 : sigmaFactor (1119 : Fin 1536) ≤ ((26283 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-19443501 / 857600 : ℚ) : ℝ) - Real.exp ((-623389657 / 27443200 : ℚ) : ℝ)) ≤ ((26283 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1119 : sigmaPower (1119 : Fin 1536) ≤ ((62288591861145 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1120 : sigmaFactor (1120 : Fin 1536) ≤ ((27029 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-58246881 / 2572288 : ℚ) : ℝ) - Real.exp ((-1823723 / 80384 : ℚ) : ℝ)) ≤ ((27029 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1120 : sigmaPower (1120 : Fin 1536) ≤ ((62151587214243 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1121 : sigmaFactor (1121 : Fin 1536) ≤ ((27797 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-930612859 / 41148416 : ℚ) : ℝ) - Real.exp ((-1864817163 / 82296832 : ℚ) : ℝ)) ≤ ((27797 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1121 : sigmaPower (1121 : Fin 1536) ≤ ((62014528016417 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1122 : sigmaFactor (1122 : Fin 1536) ≤ ((14293 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-309758779 / 13713408 : ℚ) : ℝ) - Real.exp ((-155178617 / 6856704 : ℚ) : ℝ)) ≤ ((14293 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1122 : sigmaPower (1122 : Fin 1536) ≤ ((61877414235079 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1123 : sigmaFactor (1123 : Fin 1536) ≤ ((29397 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-463970265 / 20566016 : ℚ) : ℝ) - Real.exp ((-1859471075 / 82264064 : ℚ) : ℝ)) ≤ ((29397 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1123 : sigmaPower (1123 : Fin 1536) ≤ ((3858765364851 / 17592186044416 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1124 : sigmaFactor (1124 : Fin 1536) ≤ ((15115 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-463302719 / 20561920 : ℚ) : ℝ) - Real.exp ((-116050011 / 5140480 : ℚ) : ℝ)) ≤ ((15115 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1124 : sigmaPower (1124 : Fin 1536) ≤ ((30801511395695 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1125 : sigmaFactor (1125 : Fin 1536) ≤ ((1943 / 17592186044416 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-308423687 / 13705216 : ℚ) : ℝ) - Real.exp ((-618043569 / 27410432 : ℚ) : ℝ)) ≤ ((1943 / 17592186044416 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1125 : sigmaPower (1125 : Fin 1536) ≤ ((30732872531867 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1126 : sigmaFactor (1126 : Fin 1536) ≤ ((31969 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-923937399 / 41107456 : ℚ) : ℝ) - Real.exp ((-462865667 / 20553728 : ℚ) : ℝ)) ≤ ((31969 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1126 : sigmaPower (1126 : Fin 1536) ≤ ((30664206310979 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1127 : sigmaFactor (1127 : Fin 1536) ≤ ((32875 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-230651113 / 10274816 : ℚ) : ℝ) - Real.exp ((-1848796059 / 82198528 : ℚ) : ℝ)) ≤ ((32875 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1127 : sigmaPower (1127 : Fin 1536) ≤ ((61191025433345 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1128 : sigmaFactor (1128 : Fin 1536) ≤ ((33807 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-6979335 / 311296 : ℚ) : ℝ) - Real.exp ((-874115 / 38912 : ℚ) : ℝ)) ≤ ((33807 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1128 : sigmaPower (1128 : Fin 1536) ≤ ((61053583465151 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1129 : sigmaFactor (1129 : Fin 1536) ≤ ((34765 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-54114159 / 2416640 : ℚ) : ℝ) - Real.exp ((-108439243 / 4833280 : ℚ) : ℝ)) ≤ ((34765 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1129 : sigmaPower (1129 : Fin 1536) ≤ ((30458043342303 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1130 : sigmaFactor (1130 : Fin 1536) ≤ ((17875 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-918609901 / 41074688 : ℚ) : ℝ) - Real.exp ((-460201203 / 20537344 : ℚ) : ℝ)) ≤ ((17875 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1130 : sigmaPower (1130 : Fin 1536) ≤ ((15194633764729 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1131 : sigmaFactor (1131 : Fin 1536) ≤ ((18381 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-152879969 / 6844416 : ℚ) : ℝ) - Real.exp ((-612714641 / 27377664 : ℚ) : ℝ)) ≤ ((18381 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1131 : sigmaPower (1131 : Fin 1536) ≤ ((60640928555259 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1132 : sigmaFactor (1132 : Fin 1536) ≤ ((37803 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-457975221 / 20529152 : ℚ) : ℝ) - Real.exp ((-114717779 / 5132288 : ℚ) : ℝ)) ≤ ((37803 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1132 : sigmaPower (1132 : Fin 1536) ≤ ((60503267140785 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1133 : sigmaFactor (1133 : Fin 1536) ≤ ((38873 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-914621785 / 41050112 : ℚ) : ℝ) - Real.exp ((-1832826435 / 82100224 : ℚ) : ℝ)) ≤ ((38873 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1133 : sigmaPower (1133 : Fin 1536) ≤ ((30182775391311 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1134 : sigmaFactor (1134 : Fin 1536) ≤ ((39973 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-304431281 / 13680640 : ℚ) : ℝ) - Real.exp ((-152514153 / 6840320 : ℚ) : ℝ)) ≤ ((39973 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1134 : sigmaPower (1134 : Fin 1536) ≤ ((60227779447869 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1135 : sigmaFactor (1135 : Fin 1536) ≤ ((2569 / 17592186044416 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-113995827 / 5129216 : ℚ) : ℝ) - Real.exp ((-1827514667 / 82067456 : ℚ) : ℝ)) ≤ ((2569 / 17592186044416 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1135 : sigmaPower (1135 : Fin 1536) ≤ ((3755622068975 / 17592186044416 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1136 : sigmaFactor (1136 : Fin 1536) ≤ ((42267 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-113830013 / 5128192 : ℚ) : ℝ) - Real.exp ((-7128363 / 320512 : ℚ) : ℝ)) ≤ ((42267 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1136 : sigmaPower (1136 : Fin 1536) ≤ ((14988017929215 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1137 : sigmaFactor (1137 : Fin 1536) ≤ ((21731 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-303104769 / 13672448 : ℚ) : ℝ) - Real.exp ((-607402873 / 27344896 : ℚ) : ℝ)) ≤ ((21731 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1137 : sigmaPower (1137 : Fin 1536) ≤ ((3738383453417 / 17592186044416 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1138 : sigmaFactor (1138 : Fin 1536) ≤ ((44691 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-907989225 / 41009152 : ℚ) : ℝ) - Real.exp ((-454889435 / 20504576 : ℚ) : ℝ)) ≤ ((44691 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1138 : sigmaPower (1138 : Fin 1536) ≤ ((14919035921007 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1139 : sigmaFactor (1139 : Fin 1536) ≤ ((45955 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-41212039 / 1863680 : ℚ) : ℝ) - Real.exp ((-165173481 / 7454720 : ℚ) : ℝ)) ≤ ((45955 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1139 : sigmaPower (1139 : Fin 1536) ≤ ((29769048485949 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1140 : sigmaFactor (1140 : Fin 1536) ≤ ((23627 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-150890201 / 6832128 : ℚ) : ℝ) - Real.exp ((-37797089 / 1708032 : ℚ) : ℝ)) ≤ ((23627 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1140 : sigmaPower (1140 : Fin 1536) ≤ ((59399995085223 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1141 : sigmaFactor (1141 : Fin 1536) ≤ ((48589 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-904018269 / 40984576 : ℚ) : ℝ) - Real.exp ((-1811613683 / 81969152 : ℚ) : ℝ)) ≤ ((48589 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1141 : sigmaPower (1141 : Fin 1536) ≤ ((59261837990917 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1142 : sigmaFactor (1142 : Fin 1536) ≤ ((49961 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-902696047 / 40976384 : ℚ) : ℝ) - Real.exp ((-452242131 / 20488192 : ℚ) : ℝ)) ≤ ((49961 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1142 : sigmaPower (1142 : Fin 1536) ≤ ((59123625655871 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1143 : sigmaFactor (1143 : Fin 1536) ≤ ((12843 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-75114545 / 3414016 : ℚ) : ℝ) - Real.exp ((-602108265 / 27312128 : ℚ) : ℝ)) ≤ ((12843 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1143 : sigmaPower (1143 : Fin 1536) ≤ ((58985358046945 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1144 : sigmaFactor (1144 : Fin 1536) ≤ ((52823 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-225013437 / 10240000 : ℚ) : ℝ) - Real.exp ((-28182539 / 1280000 : ℚ) : ℝ)) ≤ ((52823 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1144 : sigmaPower (1144 : Fin 1536) ≤ ((58847035130975 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1145 : sigmaFactor (1145 : Fin 1536) ≤ ((27157 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-898733671 / 40951808 : ℚ) : ℝ) - Real.exp ((-1801041627 / 81903616 : ℚ) : ℝ)) ≤ ((27157 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1145 : sigmaPower (1145 : Fin 1536) ≤ ((58708656874771 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1146 : sigmaFactor (1146 : Fin 1536) ≤ ((55847 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-17596359 / 802816 : ℚ) : ℝ) - Real.exp ((-8815697 / 401408 : ℚ) : ℝ)) ≤ ((55847 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1146 : sigmaPower (1146 : Fin 1536) ≤ ((58570223245115 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1147 : sigmaFactor (1147 : Fin 1536) ≤ ((57423 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-448047831 / 20467712 : ℚ) : ℝ) - Real.exp ((-1795764179 / 81870848 : ℚ) : ℝ)) ≤ ((57423 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1147 : sigmaPower (1147 : Fin 1536) ≤ ((58431734208763 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1148 : sigmaFactor (1148 : Fin 1536) ≤ ((59043 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-447388865 / 20463616 : ℚ) : ℝ) - Real.exp ((-112070475 / 5115904 : ℚ) : ℝ)) ≤ ((59043 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1148 : sigmaPower (1148 : Fin 1536) ≤ ((58293189732445 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1149 : sigmaFactor (1149 : Fin 1536) ≤ ((15177 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-297820171 / 13639680 : ℚ) : ℝ) - Real.exp ((-596830817 / 27279360 : ℚ) : ℝ)) ≤ ((15177 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1149 : sigmaPower (1149 : Fin 1536) ≤ ((58154589782863 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1150 : sigmaFactor (1150 : Fin 1536) ≤ ((15605 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-81104001 / 3719168 : ℚ) : ℝ) - Real.exp ((-40633153 / 1859584 : ℚ) : ℝ)) ≤ ((15605 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1150 : sigmaPower (1150 : Fin 1536) ≤ ((58015934326693 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1151 : sigmaFactor (1151 : Fin 1536) ≤ ((16045 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((307 / 20 : ℚ) : ℝ) * (Real.exp ((-13919191 / 639104 : ℚ) : ℝ) - Real.exp ((-1785226443 / 81805312 : ℚ) : ℝ)) ≤ ((16045 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1151 : sigmaPower (1151 : Fin 1536) ≤ ((57877223330585 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

end LegendreK6.M2Pilot.Enclosures.Sigma008
