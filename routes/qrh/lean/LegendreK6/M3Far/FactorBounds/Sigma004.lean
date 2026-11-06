import LegendreK6.M3Far.Enclosures.Sigma004
import LegendreK6.M3FarIntegerData

/-! Join checked analytic enclosures to the exact dyadic witness table. -/
namespace LegendreK6.M3Far.FactorBounds.Sigma004
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem bounds (i : Fin 384) (hlo : 128 ≤ i.val) (hhi : i.val < 160) :
    sigmaFactor i ≤ sigmaDyadicFactor i ∧ sigmaPower i ≤ sigmaDyadicPower i := by
  interval_cases hi : i.val
  · have heq : i = (128 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_128.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_128.trans
      change ((136472715980925 / 281474976710656 : ℚ) : ℝ) ≤ ((136472715980925 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (129 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_129.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_129.trans
      change ((136036236079067 / 281474976710656 : ℚ) : ℝ) ≤ ((136036236079067 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (130 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_130.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_130.trans
      change ((67799567647707 / 140737488355328 : ℚ) : ℝ) ≤ ((135599135295414 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (131 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_131.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_131.trans
      change ((8447588269015 / 17592186044416 : ℚ) : ℝ) ≤ ((135161412304240 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (132 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_132.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_132.trans
      change ((134723065776041 / 281474976710656 : ℚ) : ℝ) ≤ ((134723065776041 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (133 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_133.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_133.trans
      change ((33571023594381 / 70368744177664 : ℚ) : ℝ) ≤ ((134284094377524 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (134 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_134.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_134.trans
      change ((16730562096449 / 35184372088832 : ℚ) : ℝ) ≤ ((133844496771592 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (135 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_135.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_135.trans
      change ((8337766976083 / 17592186044416 : ℚ) : ℝ) ≤ ((133404271617328 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (136 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_136.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_136.trans
      change ((132963417569987 / 281474976710656 : ℚ) : ℝ) ≤ ((132963417569987 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (137 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_137.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_137.trans
      change ((8282620830061 / 17592186044416 : ℚ) : ℝ) ≤ ((132521933280976 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (138 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_138.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_138.trans
      change ((16509977174731 / 35184372088832 : ℚ) : ℝ) ≤ ((132079817397848 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (139 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_139.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_139.trans
      change ((65818534282139 / 140737488355328 : ℚ) : ℝ) ≤ ((131637068564278 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (140 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_140.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_140.trans
      change ((65596842710029 / 140737488355328 : ℚ) : ℝ) ≤ ((131193685420058 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (141 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_141.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_141.trans
      change ((130749666601079 / 281474976710656 : ℚ) : ℝ) ≤ ((130749666601079 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (142 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_142.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_142.trans
      change ((130305010739319 / 281474976710656 : ℚ) : ℝ) ≤ ((130305010739319 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (143 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_143.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_143.trans
      change ((129859716462825 / 281474976710656 : ℚ) : ℝ) ≤ ((129859716462825 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (144 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_144.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_144.trans
      change ((16176722799463 / 35184372088832 : ℚ) : ℝ) ≤ ((129413782395704 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (145 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_145.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_145.trans
      change ((64483603579053 / 140737488355328 : ℚ) : ℝ) ≤ ((128967207158106 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (146 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_146.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_146.trans
      change ((128519989366209 / 281474976710656 : ℚ) : ℝ) ≤ ((128519989366209 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (147 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_147.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_147.trans
      change ((128072127632207 / 281474976710656 : ℚ) : ℝ) ≤ ((128072127632207 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (148 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_148.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_148.trans
      change ((63811810282147 / 140737488355328 : ℚ) : ℝ) ≤ ((127623620564294 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (149 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_149.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_149.trans
      change ((127174466766651 / 281474976710656 : ℚ) : ℝ) ≤ ((127174466766651 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (150 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_150.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_150.trans
      change ((63362332419715 / 140737488355328 : ℚ) : ℝ) ≤ ((126724664839430 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (151 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_151.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_151.trans
      change ((31568553344685 / 70368744177664 : ℚ) : ℝ) ≤ ((126274213378740 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (152 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_152.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_152.trans
      change ((125823110976633 / 281474976710656 : ℚ) : ℝ) ≤ ((125823110976633 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (153 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_153.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_153.trans
      change ((3917854881909 / 8796093022208 : ℚ) : ℝ) ≤ ((125371356221088 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (154 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_154.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_154.trans
      change ((62459473847999 / 140737488355328 : ℚ) : ℝ) ≤ ((124918947695998 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (155 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_155.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_155.trans
      change ((124465883981155 / 281474976710656 : ℚ) : ℝ) ≤ ((124465883981155 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (156 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_156.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_156.trans
      change ((15501520456529 / 35184372088832 : ℚ) : ℝ) ≤ ((124012163652232 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (157 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_157.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_157.trans
      change ((30889446320193 / 70368744177664 : ℚ) : ℝ) ≤ ((123557785280772 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (158 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_158.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_158.trans
      change ((30775686858543 / 70368744177664 : ℚ) : ℝ) ≤ ((123102747434172 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (159 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma004.sigma_factor_upper_159.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma004.sigma_power_upper_159.trans
      change ((30661762168917 / 70368744177664 : ℚ) : ℝ) ≤ ((122647048675668 : ℕ) : ℝ) / 2^48
      norm_num
end LegendreK6.M3Far.FactorBounds.Sigma004
