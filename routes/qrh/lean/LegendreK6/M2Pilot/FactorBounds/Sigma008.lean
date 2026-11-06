import LegendreK6.M2Pilot.Enclosures.Sigma008
import LegendreK6.M2PilotIntegerData

/-! Join checked analytic enclosures to the exact dyadic witness table. -/
namespace LegendreK6.M2Pilot.FactorBounds.Sigma008
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem bounds (i : Fin 1536) (hlo : 1024 ≤ i.val) (hhi : i.val < 1152) :
    sigmaFactor i ≤ sigmaDyadicFactor i ∧ sigmaPower i ≤ sigmaDyadicPower i := by
  interval_cases hi : i.val
  · have heq : i = (1024 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1024.trans
      change ((1789 / 281474976710656 : ℚ) : ℝ) ≤ ((1789 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1024.trans
      change ((75059993789509 / 281474976710656 : ℚ) : ℝ) ≤ ((75059993789509 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1025 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1025.trans
      change ((1841 / 281474976710656 : ℚ) : ℝ) ≤ ((1841 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1025.trans
      change ((37464013309669 / 140737488355328 : ℚ) : ℝ) ≤ ((74928026619338 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1026 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1026.trans
      change ((947 / 140737488355328 : ℚ) : ℝ) ≤ ((1894 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1026.trans
      change ((37398003939673 / 140737488355328 : ℚ) : ℝ) ≤ ((74796007879346 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1027 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1027.trans
      change ((1949 / 281474976710656 : ℚ) : ℝ) ≤ ((1949 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1027.trans
      change ((18665984384825 / 70368744177664 : ℚ) : ℝ) ≤ ((74663937539300 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1028 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1028.trans
      change ((1003 / 140737488355328 : ℚ) : ℝ) ≤ ((2006 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1028.trans
      change ((74531815568941 / 281474976710656 : ℚ) : ℝ) ≤ ((74531815568941 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1029 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1029.trans
      change ((129 / 17592186044416 : ℚ) : ℝ) ≤ ((2064 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1029.trans
      change ((18599910484497 / 70368744177664 : ℚ) : ℝ) ≤ ((74399641937988 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1030 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1030.trans
      change ((2123 / 281474976710656 : ℚ) : ℝ) ≤ ((2123 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1030.trans
      change ((74267416616135 / 281474976710656 : ℚ) : ℝ) ≤ ((74267416616135 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1031 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1031.trans
      change ((2185 / 281474976710656 : ℚ) : ℝ) ≤ ((2185 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1031.trans
      change ((74135139573053 / 281474976710656 : ℚ) : ℝ) ≤ ((74135139573053 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1032 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1032.trans
      change ((281 / 35184372088832 : ℚ) : ℝ) ≤ ((2248 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1032.trans
      change ((74002810778389 / 281474976710656 : ℚ) : ℝ) ≤ ((74002810778389 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1033 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1033.trans
      change ((2313 / 281474976710656 : ℚ) : ℝ) ≤ ((2313 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1033.trans
      change ((73870430201767 / 281474976710656 : ℚ) : ℝ) ≤ ((73870430201767 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1034 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1034.trans
      change ((595 / 70368744177664 : ℚ) : ℝ) ≤ ((2380 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1034.trans
      change ((36868998906393 / 140737488355328 : ℚ) : ℝ) ≤ ((73737997812786 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1035 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1035.trans
      change ((2449 / 281474976710656 : ℚ) : ℝ) ≤ ((2449 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1035.trans
      change ((36802756790511 / 140737488355328 : ℚ) : ℝ) ≤ ((73605513581022 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1036 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1036.trans
      change ((315 / 35184372088832 : ℚ) : ℝ) ≤ ((2520 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1036.trans
      change ((73472977476027 / 281474976710656 : ℚ) : ℝ) ≤ ((73472977476027 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1037 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1037.trans
      change ((81 / 8796093022208 : ℚ) : ℝ) ≤ ((2592 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1037.trans
      change ((73340389467329 / 281474976710656 : ℚ) : ℝ) ≤ ((73340389467329 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1038 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1038.trans
      change ((2667 / 281474976710656 : ℚ) : ℝ) ≤ ((2667 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1038.trans
      change ((73207749524433 / 281474976710656 : ℚ) : ℝ) ≤ ((73207749524433 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1039 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1039.trans
      change ((343 / 35184372088832 : ℚ) : ℝ) ≤ ((2744 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1039.trans
      change ((73075057616819 / 281474976710656 : ℚ) : ℝ) ≤ ((73075057616819 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1040 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1040.trans
      change ((353 / 35184372088832 : ℚ) : ℝ) ≤ ((2824 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1040.trans
      change ((72942313713943 / 281474976710656 : ℚ) : ℝ) ≤ ((72942313713943 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1041 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1041.trans
      change ((2905 / 281474976710656 : ℚ) : ℝ) ≤ ((2905 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1041.trans
      change ((36404758892619 / 140737488355328 : ℚ) : ℝ) ≤ ((72809517785238 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1042 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1042.trans
      change ((2989 / 281474976710656 : ℚ) : ℝ) ≤ ((2989 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1042.trans
      change ((4542291862507 / 17592186044416 : ℚ) : ℝ) ≤ ((72676669800112 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1043 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1043.trans
      change ((3075 / 281474976710656 : ℚ) : ℝ) ≤ ((3075 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1043.trans
      change ((72543769727951 / 281474976710656 : ℚ) : ℝ) ≤ ((72543769727951 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1044 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1044.trans
      change ((791 / 70368744177664 : ℚ) : ℝ) ≤ ((3164 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1044.trans
      change ((36205408769057 / 140737488355328 : ℚ) : ℝ) ≤ ((72410817538114 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1045 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1045.trans
      change ((3255 / 281474976710656 : ℚ) : ℝ) ≤ ((3255 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1045.trans
      change ((72277813199939 / 281474976710656 : ℚ) : ℝ) ≤ ((72277813199939 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1046 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1046.trans
      change ((3349 / 281474976710656 : ℚ) : ℝ) ≤ ((3349 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1046.trans
      change ((72144756682737 / 281474976710656 : ℚ) : ℝ) ≤ ((72144756682737 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1047 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1047.trans
      change ((1723 / 140737488355328 : ℚ) : ℝ) ≤ ((3446 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1047.trans
      change ((72011647955797 / 281474976710656 : ℚ) : ℝ) ≤ ((72011647955797 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1048 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1048.trans
      change ((3545 / 281474976710656 : ℚ) : ℝ) ≤ ((3545 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1048.trans
      change ((2246202718387 / 8796093022208 : ℚ) : ℝ) ≤ ((71878486988384 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1049 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1049.trans
      change ((57 / 4398046511104 : ℚ) : ℝ) ≤ ((3648 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1049.trans
      change ((71745273749737 / 281474976710656 : ℚ) : ℝ) ≤ ((71745273749737 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1050 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1050.trans
      change ((3753 / 281474976710656 : ℚ) : ℝ) ≤ ((3753 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1050.trans
      change ((4475750513067 / 17592186044416 : ℚ) : ℝ) ≤ ((71612008209072 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1051 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1051.trans
      change ((3861 / 281474976710656 : ℚ) : ℝ) ≤ ((3861 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1051.trans
      change ((35739345167791 / 140737488355328 : ℚ) : ℝ) ≤ ((71478690335582 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1052 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1052.trans
      change ((993 / 70368744177664 : ℚ) : ℝ) ≤ ((3972 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1052.trans
      change ((71345320098433 / 281474976710656 : ℚ) : ℝ) ≤ ((71345320098433 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1053 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1053.trans
      change ((4087 / 281474976710656 : ℚ) : ℝ) ≤ ((4087 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1053.trans
      change ((35605948733385 / 140737488355328 : ℚ) : ℝ) ≤ ((71211897466770 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1054 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1054.trans
      change ((1051 / 70368744177664 : ℚ) : ℝ) ≤ ((4204 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1054.trans
      change ((4442401400607 / 17592186044416 : ℚ) : ℝ) ≤ ((71078422409712 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1055 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1055.trans
      change ((4325 / 281474976710656 : ℚ) : ℝ) ≤ ((4325 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1055.trans
      change ((2217027965511 / 8796093022208 : ℚ) : ℝ) ≤ ((70944894896352 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1056 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1056.trans
      change ((2225 / 140737488355328 : ℚ) : ℝ) ≤ ((4450 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1056.trans
      change ((70811314895763 / 281474976710656 : ℚ) : ℝ) ≤ ((70811314895763 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1057 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1057.trans
      change ((2289 / 140737488355328 : ℚ) : ℝ) ≤ ((4578 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1057.trans
      change ((35338841188495 / 140737488355328 : ℚ) : ℝ) ≤ ((70677682376990 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1058 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1058.trans
      change ((2355 / 140737488355328 : ℚ) : ℝ) ≤ ((4710 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1058.trans
      change ((70543997309055 / 281474976710656 : ℚ) : ℝ) ≤ ((70543997309055 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1059 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1059.trans
      change ((4845 / 281474976710656 : ℚ) : ℝ) ≤ ((4845 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1059.trans
      change ((70410259660955 / 281474976710656 : ℚ) : ℝ) ≤ ((70410259660955 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1060 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1060.trans
      change ((4985 / 281474976710656 : ℚ) : ℝ) ≤ ((4985 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1060.trans
      change ((1098069834401 / 4398046511104 : ℚ) : ℝ) ≤ ((70276469401664 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1061 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1061.trans
      change ((641 / 35184372088832 : ℚ) : ℝ) ≤ ((5128 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1061.trans
      change ((70142626500131 / 281474976710656 : ℚ) : ℝ) ≤ ((70142626500131 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1062 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1062.trans
      change ((5275 / 281474976710656 : ℚ) : ℝ) ≤ ((5275 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1062.trans
      change ((2187772841415 / 8796093022208 : ℚ) : ℝ) ≤ ((70008730925280 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1063 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1063.trans
      change ((5427 / 281474976710656 : ℚ) : ℝ) ≤ ((5427 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1063.trans
      change ((34937391323005 / 140737488355328 : ℚ) : ℝ) ≤ ((69874782646010 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1064 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1064.trans
      change ((5583 / 281474976710656 : ℚ) : ℝ) ≤ ((5583 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1064.trans
      change ((69740781631197 / 281474976710656 : ℚ) : ℝ) ≤ ((69740781631197 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1065 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1065.trans
      change ((5743 / 281474976710656 : ℚ) : ℝ) ≤ ((5743 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1065.trans
      change ((17401681962423 / 70368744177664 : ℚ) : ℝ) ≤ ((69606727849692 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1066 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1066.trans
      change ((1477 / 70368744177664 : ℚ) : ℝ) ≤ ((5908 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1066.trans
      change ((69472621270321 / 281474976710656 : ℚ) : ℝ) ≤ ((69472621270321 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1067 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1067.trans
      change ((3039 / 140737488355328 : ℚ) : ℝ) ≤ ((6078 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1067.trans
      change ((34669230930943 / 140737488355328 : ℚ) : ℝ) ≤ ((69338461861886 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1068 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1068.trans
      change ((6253 / 281474976710656 : ℚ) : ℝ) ≤ ((6253 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1068.trans
      change ((17301062398291 / 70368744177664 : ℚ) : ℝ) ≤ ((69204249593164 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1069 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1069.trans
      change ((201 / 8796093022208 : ℚ) : ℝ) ≤ ((6432 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1069.trans
      change ((17267496108227 / 70368744177664 : ℚ) : ℝ) ≤ ((69069984432908 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1070 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1070.trans
      change ((6617 / 281474976710656 : ℚ) : ℝ) ≤ ((6617 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1070.trans
      change ((68935666349845 / 281474976710656 : ℚ) : ℝ) ≤ ((68935666349845 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1071 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1071.trans
      change ((6807 / 281474976710656 : ℚ) : ℝ) ≤ ((6807 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1071.trans
      change ((34400647656339 / 140737488355328 : ℚ) : ℝ) ≤ ((68801295312678 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1072 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1072.trans
      change ((3501 / 140737488355328 : ℚ) : ℝ) ≤ ((7002 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1072.trans
      change ((68666871290087 / 281474976710656 : ℚ) : ℝ) ≤ ((68666871290087 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1073 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1073.trans
      change ((7203 / 281474976710656 : ℚ) : ℝ) ≤ ((7203 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1073.trans
      change ((68532394250725 / 281474976710656 : ℚ) : ℝ) ≤ ((68532394250725 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1074 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1074.trans
      change ((3705 / 140737488355328 : ℚ) : ℝ) ≤ ((7410 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1074.trans
      change ((68397864163221 / 281474976710656 : ℚ) : ℝ) ≤ ((68397864163221 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1075 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1075.trans
      change ((3811 / 140737488355328 : ℚ) : ℝ) ≤ ((7622 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1075.trans
      change ((17065820249045 / 70368744177664 : ℚ) : ℝ) ≤ ((68263280996180 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1076 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1076.trans
      change ((7841 / 281474976710656 : ℚ) : ℝ) ≤ ((7841 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1076.trans
      change ((68128644718181 / 281474976710656 : ℚ) : ℝ) ≤ ((68128644718181 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1077 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1077.trans
      change ((8065 / 281474976710656 : ℚ) : ℝ) ≤ ((8065 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1077.trans
      change ((67993955297779 / 281474976710656 : ℚ) : ℝ) ≤ ((67993955297779 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1078 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1078.trans
      change ((1037 / 35184372088832 : ℚ) : ℝ) ≤ ((8296 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1078.trans
      change ((4241200793969 / 17592186044416 : ℚ) : ℝ) ≤ ((67859212703504 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1079 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1079.trans
      change ((4267 / 140737488355328 : ℚ) : ℝ) ≤ ((8534 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1079.trans
      change ((67724416903861 / 281474976710656 : ℚ) : ℝ) ≤ ((67724416903861 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1080 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1080.trans
      change ((4389 / 140737488355328 : ℚ) : ℝ) ≤ ((8778 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1080.trans
      change ((33794783933665 / 140737488355328 : ℚ) : ℝ) ≤ ((67589567867330 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1081 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1081.trans
      change ((4515 / 140737488355328 : ℚ) : ℝ) ≤ ((9030 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1081.trans
      change ((67454665562367 / 281474976710656 : ℚ) : ℝ) ≤ ((67454665562367 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1082 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1082.trans
      change ((1161 / 35184372088832 : ℚ) : ℝ) ≤ ((9288 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1082.trans
      change ((33659854978701 / 140737488355328 : ℚ) : ℝ) ≤ ((67319709957402 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1083 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1083.trans
      change ((4777 / 140737488355328 : ℚ) : ℝ) ≤ ((9554 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1083.trans
      change ((67184701020841 / 281474976710656 : ℚ) : ℝ) ≤ ((67184701020841 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1084 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1084.trans
      change ((2457 / 70368744177664 : ℚ) : ℝ) ≤ ((9828 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1084.trans
      change ((67049638721063 / 281474976710656 : ℚ) : ℝ) ≤ ((67049638721063 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1085 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1085.trans
      change ((10109 / 281474976710656 : ℚ) : ℝ) ≤ ((10109 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1085.trans
      change ((66914523026425 / 281474976710656 : ℚ) : ℝ) ≤ ((66914523026425 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1086 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1086.trans
      change ((5199 / 140737488355328 : ℚ) : ℝ) ≤ ((10398 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1086.trans
      change ((66779353905257 / 281474976710656 : ℚ) : ℝ) ≤ ((66779353905257 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1087 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1087.trans
      change ((10695 / 281474976710656 : ℚ) : ℝ) ≤ ((10695 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1087.trans
      change ((8330516415733 / 35184372088832 : ℚ) : ℝ) ≤ ((66644131325864 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1088 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1088.trans
      change ((11001 / 281474976710656 : ℚ) : ℝ) ≤ ((11001 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1088.trans
      change ((66508855256527 / 281474976710656 : ℚ) : ℝ) ≤ ((66508855256527 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1089 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1089.trans
      change ((2829 / 70368744177664 : ℚ) : ℝ) ≤ ((11316 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1089.trans
      change ((16593381416375 / 70368744177664 : ℚ) : ℝ) ≤ ((66373525665500 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1090 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1090.trans
      change ((11639 / 281474976710656 : ℚ) : ℝ) ≤ ((11639 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1090.trans
      change ((66238142521015 / 281474976710656 : ℚ) : ℝ) ≤ ((66238142521015 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1091 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1091.trans
      change ((2993 / 70368744177664 : ℚ) : ℝ) ≤ ((11972 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1091.trans
      change ((66102705791275 / 281474976710656 : ℚ) : ℝ) ≤ ((66102705791275 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1092 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1092.trans
      change ((6157 / 140737488355328 : ℚ) : ℝ) ≤ ((12314 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1092.trans
      change ((65967215444461 / 281474976710656 : ℚ) : ℝ) ≤ ((65967215444461 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1093 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1093.trans
      change ((12665 / 281474976710656 : ℚ) : ℝ) ≤ ((12665 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1093.trans
      change ((8228958931091 / 35184372088832 : ℚ) : ℝ) ≤ ((65831671448728 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1094 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1094.trans
      change ((13027 / 281474976710656 : ℚ) : ℝ) ≤ ((13027 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1094.trans
      change ((16424018443051 / 70368744177664 : ℚ) : ℝ) ≤ ((65696073772204 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1095 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1095.trans
      change ((13399 / 281474976710656 : ℚ) : ℝ) ≤ ((13399 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1095.trans
      change ((65560422382993 / 281474976710656 : ℚ) : ℝ) ≤ ((65560422382993 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1096 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1096.trans
      change ((6891 / 140737488355328 : ℚ) : ℝ) ≤ ((13782 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1096.trans
      change ((8178089656147 / 35184372088832 : ℚ) : ℝ) ≤ ((65424717249176 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1097 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1097.trans
      change ((14175 / 281474976710656 : ℚ) : ℝ) ≤ ((14175 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1097.trans
      change ((16322239584701 / 70368744177664 : ℚ) : ℝ) ≤ ((65288958338804 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1098 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1098.trans
      change ((14579 / 281474976710656 : ℚ) : ℝ) ≤ ((14579 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1098.trans
      change ((65153145619907 / 281474976710656 : ℚ) : ℝ) ≤ ((65153145619907 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1099 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1099.trans
      change ((14995 / 281474976710656 : ℚ) : ℝ) ≤ ((14995 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1099.trans
      change ((32508639530243 / 140737488355328 : ℚ) : ℝ) ≤ ((65017279060486 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1100 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1100.trans
      change ((15423 / 281474976710656 : ℚ) : ℝ) ≤ ((15423 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1100.trans
      change ((64881358628521 / 281474976710656 : ℚ) : ℝ) ≤ ((64881358628521 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1101 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1101.trans
      change ((7931 / 140737488355328 : ℚ) : ℝ) ≤ ((15862 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1101.trans
      change ((32372692145981 / 140737488355328 : ℚ) : ℝ) ≤ ((64745384291962 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1102 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1102.trans
      change ((16315 / 281474976710656 : ℚ) : ℝ) ≤ ((16315 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1102.trans
      change ((4038084751171 / 17592186044416 : ℚ) : ℝ) ≤ ((64609356018736 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1103 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1103.trans
      change ((4195 / 70368744177664 : ℚ) : ℝ) ≤ ((16780 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1103.trans
      change ((64473273776745 / 281474976710656 : ℚ) : ℝ) ≤ ((64473273776745 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1104 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1104.trans
      change ((8629 / 140737488355328 : ℚ) : ℝ) ≤ ((17258 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1104.trans
      change ((64337137533865 / 281474976710656 : ℚ) : ℝ) ≤ ((64337137533865 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1105 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1105.trans
      change ((17749 / 281474976710656 : ℚ) : ℝ) ≤ ((17749 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1105.trans
      change ((64200947257945 / 281474976710656 : ℚ) : ℝ) ≤ ((64200947257945 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1106 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1106.trans
      change ((18255 / 281474976710656 : ℚ) : ℝ) ≤ ((18255 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1106.trans
      change ((32032351458405 / 140737488355328 : ℚ) : ℝ) ≤ ((64064702916810 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1107 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1107.trans
      change ((18775 / 281474976710656 : ℚ) : ℝ) ≤ ((18775 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1107.trans
      change ((63928404478259 / 281474976710656 : ℚ) : ℝ) ≤ ((63928404478259 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1108 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1108.trans
      change ((19309 / 281474976710656 : ℚ) : ℝ) ≤ ((19309 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1108.trans
      change ((63792051910067 / 281474976710656 : ℚ) : ℝ) ≤ ((63792051910067 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1109 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1109.trans
      change ((19859 / 281474976710656 : ℚ) : ℝ) ≤ ((19859 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1109.trans
      change ((63655645179981 / 281474976710656 : ℚ) : ℝ) ≤ ((63655645179981 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1110 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1110.trans
      change ((2553 / 35184372088832 : ℚ) : ℝ) ≤ ((20424 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1110.trans
      change ((63519184255723 / 281474976710656 : ℚ) : ℝ) ≤ ((63519184255723 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1111 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1111.trans
      change ((21005 / 281474976710656 : ℚ) : ℝ) ≤ ((21005 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1111.trans
      change ((31691334552495 / 140737488355328 : ℚ) : ℝ) ≤ ((63382669104990 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1112 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1112.trans
      change ((10801 / 140737488355328 : ℚ) : ℝ) ≤ ((21602 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1112.trans
      change ((63246099695453 / 281474976710656 : ℚ) : ℝ) ≤ ((63246099695453 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1113 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1113.trans
      change ((2777 / 35184372088832 : ℚ) : ℝ) ≤ ((22216 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1113.trans
      change ((63109475994757 / 281474976710656 : ℚ) : ℝ) ≤ ((63109475994757 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1114 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1114.trans
      change ((357 / 4398046511104 : ℚ) : ℝ) ≤ ((22848 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1114.trans
      change ((31486398985261 / 140737488355328 : ℚ) : ℝ) ≤ ((62972797970522 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1115 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1115.trans
      change ((23497 / 281474976710656 : ℚ) : ℝ) ≤ ((23497 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1115.trans
      change ((31418032795171 / 140737488355328 : ℚ) : ℝ) ≤ ((62836065590342 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1116 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1116.trans
      change ((24165 / 281474976710656 : ℚ) : ℝ) ≤ ((24165 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1116.trans
      change ((62699278821785 / 281474976710656 : ℚ) : ℝ) ≤ ((62699278821785 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1117 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1117.trans
      change ((6213 / 70368744177664 : ℚ) : ℝ) ≤ ((24852 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1117.trans
      change ((31281218816197 / 140737488355328 : ℚ) : ℝ) ≤ ((62562437632394 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1118 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1118.trans
      change ((25557 / 281474976710656 : ℚ) : ℝ) ≤ ((25557 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1118.trans
      change ((62425541989683 / 281474976710656 : ℚ) : ℝ) ≤ ((62425541989683 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1119 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1119.trans
      change ((26283 / 281474976710656 : ℚ) : ℝ) ≤ ((26283 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1119.trans
      change ((62288591861145 / 281474976710656 : ℚ) : ℝ) ≤ ((62288591861145 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1120 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1120.trans
      change ((27029 / 281474976710656 : ℚ) : ℝ) ≤ ((27029 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1120.trans
      change ((62151587214243 / 281474976710656 : ℚ) : ℝ) ≤ ((62151587214243 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1121 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1121.trans
      change ((27797 / 281474976710656 : ℚ) : ℝ) ≤ ((27797 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1121.trans
      change ((62014528016417 / 281474976710656 : ℚ) : ℝ) ≤ ((62014528016417 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1122 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1122.trans
      change ((14293 / 140737488355328 : ℚ) : ℝ) ≤ ((28586 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1122.trans
      change ((61877414235079 / 281474976710656 : ℚ) : ℝ) ≤ ((61877414235079 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1123 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1123.trans
      change ((29397 / 281474976710656 : ℚ) : ℝ) ≤ ((29397 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1123.trans
      change ((3858765364851 / 17592186044416 : ℚ) : ℝ) ≤ ((61740245837616 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1124 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1124.trans
      change ((15115 / 140737488355328 : ℚ) : ℝ) ≤ ((30230 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1124.trans
      change ((30801511395695 / 140737488355328 : ℚ) : ℝ) ≤ ((61603022791390 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1125 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1125.trans
      change ((1943 / 17592186044416 : ℚ) : ℝ) ≤ ((31088 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1125.trans
      change ((30732872531867 / 140737488355328 : ℚ) : ℝ) ≤ ((61465745063734 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1126 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1126.trans
      change ((31969 / 281474976710656 : ℚ) : ℝ) ≤ ((31969 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1126.trans
      change ((30664206310979 / 140737488355328 : ℚ) : ℝ) ≤ ((61328412621958 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1127 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1127.trans
      change ((32875 / 281474976710656 : ℚ) : ℝ) ≤ ((32875 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1127.trans
      change ((61191025433345 / 281474976710656 : ℚ) : ℝ) ≤ ((61191025433345 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1128 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1128.trans
      change ((33807 / 281474976710656 : ℚ) : ℝ) ≤ ((33807 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1128.trans
      change ((61053583465151 / 281474976710656 : ℚ) : ℝ) ≤ ((61053583465151 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1129 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1129.trans
      change ((34765 / 281474976710656 : ℚ) : ℝ) ≤ ((34765 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1129.trans
      change ((30458043342303 / 140737488355328 : ℚ) : ℝ) ≤ ((60916086684606 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1130 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1130.trans
      change ((17875 / 140737488355328 : ℚ) : ℝ) ≤ ((35750 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1130.trans
      change ((15194633764729 / 70368744177664 : ℚ) : ℝ) ≤ ((60778535058916 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1131 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1131.trans
      change ((18381 / 140737488355328 : ℚ) : ℝ) ≤ ((36762 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1131.trans
      change ((60640928555259 / 281474976710656 : ℚ) : ℝ) ≤ ((60640928555259 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1132 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1132.trans
      change ((37803 / 281474976710656 : ℚ) : ℝ) ≤ ((37803 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1132.trans
      change ((60503267140785 / 281474976710656 : ℚ) : ℝ) ≤ ((60503267140785 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1133 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1133.trans
      change ((38873 / 281474976710656 : ℚ) : ℝ) ≤ ((38873 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1133.trans
      change ((30182775391311 / 140737488355328 : ℚ) : ℝ) ≤ ((60365550782622 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1134 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1134.trans
      change ((39973 / 281474976710656 : ℚ) : ℝ) ≤ ((39973 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1134.trans
      change ((60227779447869 / 281474976710656 : ℚ) : ℝ) ≤ ((60227779447869 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1135 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1135.trans
      change ((2569 / 17592186044416 : ℚ) : ℝ) ≤ ((41104 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1135.trans
      change ((3755622068975 / 17592186044416 : ℚ) : ℝ) ≤ ((60089953103600 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1136 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1136.trans
      change ((42267 / 281474976710656 : ℚ) : ℝ) ≤ ((42267 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1136.trans
      change ((14988017929215 / 70368744177664 : ℚ) : ℝ) ≤ ((59952071716860 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1137 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1137.trans
      change ((21731 / 140737488355328 : ℚ) : ℝ) ≤ ((43462 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1137.trans
      change ((3738383453417 / 17592186044416 : ℚ) : ℝ) ≤ ((59814135254672 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1138 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1138.trans
      change ((44691 / 281474976710656 : ℚ) : ℝ) ≤ ((44691 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1138.trans
      change ((14919035921007 / 70368744177664 : ℚ) : ℝ) ≤ ((59676143684028 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1139 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1139.trans
      change ((45955 / 281474976710656 : ℚ) : ℝ) ≤ ((45955 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1139.trans
      change ((29769048485949 / 140737488355328 : ℚ) : ℝ) ≤ ((59538096971898 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1140 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1140.trans
      change ((23627 / 140737488355328 : ℚ) : ℝ) ≤ ((47254 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1140.trans
      change ((59399995085223 / 281474976710656 : ℚ) : ℝ) ≤ ((59399995085223 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1141 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1141.trans
      change ((48589 / 281474976710656 : ℚ) : ℝ) ≤ ((48589 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1141.trans
      change ((59261837990917 / 281474976710656 : ℚ) : ℝ) ≤ ((59261837990917 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1142 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1142.trans
      change ((49961 / 281474976710656 : ℚ) : ℝ) ≤ ((49961 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1142.trans
      change ((59123625655871 / 281474976710656 : ℚ) : ℝ) ≤ ((59123625655871 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1143 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1143.trans
      change ((12843 / 70368744177664 : ℚ) : ℝ) ≤ ((51372 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1143.trans
      change ((58985358046945 / 281474976710656 : ℚ) : ℝ) ≤ ((58985358046945 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1144 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1144.trans
      change ((52823 / 281474976710656 : ℚ) : ℝ) ≤ ((52823 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1144.trans
      change ((58847035130975 / 281474976710656 : ℚ) : ℝ) ≤ ((58847035130975 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1145 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1145.trans
      change ((27157 / 140737488355328 : ℚ) : ℝ) ≤ ((54314 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1145.trans
      change ((58708656874771 / 281474976710656 : ℚ) : ℝ) ≤ ((58708656874771 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1146 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1146.trans
      change ((55847 / 281474976710656 : ℚ) : ℝ) ≤ ((55847 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1146.trans
      change ((58570223245115 / 281474976710656 : ℚ) : ℝ) ≤ ((58570223245115 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1147 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1147.trans
      change ((57423 / 281474976710656 : ℚ) : ℝ) ≤ ((57423 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1147.trans
      change ((58431734208763 / 281474976710656 : ℚ) : ℝ) ≤ ((58431734208763 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1148 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1148.trans
      change ((59043 / 281474976710656 : ℚ) : ℝ) ≤ ((59043 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1148.trans
      change ((58293189732445 / 281474976710656 : ℚ) : ℝ) ≤ ((58293189732445 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1149 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1149.trans
      change ((15177 / 70368744177664 : ℚ) : ℝ) ≤ ((60708 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1149.trans
      change ((58154589782863 / 281474976710656 : ℚ) : ℝ) ≤ ((58154589782863 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1150 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1150.trans
      change ((15605 / 70368744177664 : ℚ) : ℝ) ≤ ((62420 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1150.trans
      change ((58015934326693 / 281474976710656 : ℚ) : ℝ) ≤ ((58015934326693 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1151 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_1151.trans
      change ((16045 / 70368744177664 : ℚ) : ℝ) ≤ ((64180 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_1151.trans
      change ((57877223330585 / 281474976710656 : ℚ) : ℝ) ≤ ((57877223330585 : ℕ) : ℝ) / 2^48
      norm_num
end LegendreK6.M2Pilot.FactorBounds.Sigma008
