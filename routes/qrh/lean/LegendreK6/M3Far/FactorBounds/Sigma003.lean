import LegendreK6.M3Far.Enclosures.Sigma003
import LegendreK6.M3FarIntegerData

/-! Join checked analytic enclosures to the exact dyadic witness table. -/
namespace LegendreK6.M3Far.FactorBounds.Sigma003
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem bounds (i : Fin 384) (hlo : 96 ≤ i.val) (hhi : i.val < 128) :
    sigmaFactor i ≤ sigmaDyadicFactor i ∧ sigmaPower i ≤ sigmaDyadicPower i := by
  interval_cases hi : i.val
  · have heq : i = (96 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_96.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_96.trans
      change ((150119987579017 / 281474976710656 : ℚ) : ℝ) ≤ ((150119987579017 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (97 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_97.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_97.trans
      change ((149702697828971 / 281474976710656 : ℚ) : ℝ) ≤ ((149702697828971 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (98 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_98.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_98.trans
      change ((149284827703751 / 281474976710656 : ℚ) : ℝ) ≤ ((149284827703751 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (99 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_99.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_99.trans
      change ((74433187995859 / 140737488355328 : ℚ) : ℝ) ≤ ((148866375991718 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (100 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_100.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_100.trans
      change ((74223670738929 / 140737488355328 : ℚ) : ℝ) ≤ ((148447341477858 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (101 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_101.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_101.trans
      change ((148027722943769 / 281474976710656 : ℚ) : ℝ) ≤ ((148027722943769 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (102 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_102.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_102.trans
      change ((147607519167653 / 281474976710656 : ℚ) : ℝ) ≤ ((147607519167653 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (103 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_103.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_103.trans
      change ((73593364462149 / 140737488355328 : ℚ) : ℝ) ≤ ((147186728924298 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (104 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_104.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_104.trans
      change ((146765350985073 / 281474976710656 : ℚ) : ℝ) ≤ ((146765350985073 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (105 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_105.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_105.trans
      change ((73171692058955 / 140737488355328 : ℚ) : ℝ) ≤ ((146343384117910 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (106 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_106.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_106.trans
      change ((2280012923239 / 4398046511104 : ℚ) : ℝ) ≤ ((145920827087296 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (107 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_107.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_107.trans
      change ((145497678654261 / 281474976710656 : ℚ) : ℝ) ≤ ((145497678654261 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (108 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_108.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_108.trans
      change ((145073937576361 / 281474976710656 : ℚ) : ℝ) ≤ ((145073937576361 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (109 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_109.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_109.trans
      change ((18081200325959 / 35184372088832 : ℚ) : ℝ) ≤ ((144649602607672 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (110 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_110.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_110.trans
      change ((144224672498775 / 281474976710656 : ℚ) : ℝ) ≤ ((144224672498775 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (111 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_111.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_111.trans
      change ((143799145996743 / 281474976710656 : ℚ) : ℝ) ≤ ((143799145996743 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (112 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_112.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_112.trans
      change ((143373021845129 / 281474976710656 : ℚ) : ℝ) ≤ ((143373021845129 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (113 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_113.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_113.trans
      change ((142946298783955 / 281474976710656 : ℚ) : ℝ) ≤ ((142946298783955 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (114 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_114.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_114.trans
      change ((35629743887425 / 70368744177664 : ℚ) : ℝ) ≤ ((142518975549700 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (115 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_115.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_115.trans
      change ((35522762718821 / 70368744177664 : ℚ) : ℝ) ≤ ((142091050875284 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (116 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_116.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_116.trans
      change ((70831261745029 / 140737488355328 : ℚ) : ℝ) ≤ ((141662523490058 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (117 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_117.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_117.trans
      change ((70616696059897 / 140737488355328 : ℚ) : ℝ) ≤ ((141233392119794 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (118 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_118.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_118.trans
      change ((70401827743333 / 140737488355328 : ℚ) : ℝ) ≤ ((140803655486666 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (119 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_119.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_119.trans
      change ((140373312309243 / 281474976710656 : ℚ) : ℝ) ≤ ((140373312309243 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (120 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_120.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_120.trans
      change ((69971180651237 / 140737488355328 : ℚ) : ℝ) ≤ ((139942361302474 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (121 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_121.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_121.trans
      change ((139510801177673 / 281474976710656 : ℚ) : ℝ) ≤ ((139510801177673 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (122 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_122.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_122.trans
      change ((8692414415157 / 17592186044416 : ℚ) : ℝ) ≤ ((139078630642512 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (123 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_123.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_123.trans
      change ((138645848401003 / 281474976710656 : ℚ) : ℝ) ≤ ((138645848401003 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (124 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_124.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_124.trans
      change ((69106226576743 / 140737488355328 : ℚ) : ℝ) ≤ ((138212453153486 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (125 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_125.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_125.trans
      change ((137778443596617 / 281474976710656 : ℚ) : ℝ) ≤ ((137778443596617 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (126 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_126.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_126.trans
      change ((34335954605839 / 70368744177664 : ℚ) : ℝ) ≤ ((137343818423356 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (127 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma003.sigma_factor_upper_127.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma003.sigma_power_upper_127.trans
      change ((68454288161475 / 140737488355328 : ℚ) : ℝ) ≤ ((136908576322950 : ℕ) : ℝ) / 2^48
      norm_num
end LegendreK6.M3Far.FactorBounds.Sigma003
