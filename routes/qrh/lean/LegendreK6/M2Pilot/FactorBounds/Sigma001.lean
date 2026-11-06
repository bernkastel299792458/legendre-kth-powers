import LegendreK6.M2Pilot.Enclosures.Sigma001
import LegendreK6.M2PilotIntegerData

/-! Join checked analytic enclosures to the exact dyadic witness table. -/
namespace LegendreK6.M2Pilot.FactorBounds.Sigma001
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem bounds (i : Fin 1536) (hlo : 128 ≤ i.val) (hhi : i.val < 256) :
    sigmaFactor i ≤ sigmaDyadicFactor i ∧ sigmaPower i ≤ sigmaDyadicPower i := by
  interval_cases hi : i.val
  · have heq : i = (128 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_128.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_128.trans
      change ((175672325890339 / 281474976710656 : ℚ) : ℝ) ≤ ((175672325890339 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (129 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_129.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_129.trans
      change ((87788371788727 / 140737488355328 : ℚ) : ℝ) ≤ ((175576743577454 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (130 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_130.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_130.trans
      change ((87740564738983 / 140737488355328 : ℚ) : ℝ) ≤ ((175481129477966 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (131 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_131.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_131.trans
      change ((87692741788009 / 140737488355328 : ℚ) : ℝ) ≤ ((175385483576018 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (132 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_132.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_132.trans
      change ((87644902927869 / 140737488355328 : ℚ) : ℝ) ≤ ((175289805855738 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (133 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_133.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_133.trans
      change ((2737407754707 / 4398046511104 : ℚ) : ℝ) ≤ ((175194096301248 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (134 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_134.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_134.trans
      change ((175098354896657 / 281474976710656 : ℚ) : ℝ) ≤ ((175098354896657 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (135 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_135.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_135.trans
      change ((175002581626063 / 281474976710656 : ℚ) : ℝ) ≤ ((175002581626063 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (136 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_136.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_136.trans
      change ((174906776473555 / 281474976710656 : ℚ) : ℝ) ≤ ((174906776473555 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (137 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_137.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_137.trans
      change ((87405469711605 / 140737488355328 : ℚ) : ℝ) ≤ ((174810939423210 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (138 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_138.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_138.trans
      change ((21839383807387 / 35184372088832 : ℚ) : ℝ) ≤ ((174715070459096 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (139 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_139.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_139.trans
      change ((43654792391317 / 70368744177664 : ℚ) : ℝ) ≤ ((174619169565268 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (140 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_140.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_140.trans
      change ((174523236725773 / 281474976710656 : ℚ) : ℝ) ≤ ((174523236725773 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (141 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_141.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_141.trans
      change ((174427271924645 / 281474976710656 : ℚ) : ℝ) ≤ ((174427271924645 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (142 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_142.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_142.trans
      change ((174331275145909 / 281474976710656 : ℚ) : ℝ) ≤ ((174331275145909 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (143 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_143.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_143.trans
      change ((43558811593395 / 70368744177664 : ℚ) : ℝ) ≤ ((174235246373580 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (144 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_144.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_144.trans
      change ((43534796397915 / 70368744177664 : ℚ) : ℝ) ≤ ((174139185591660 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (145 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_145.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_145.trans
      change ((174043092784141 / 281474976710656 : ℚ) : ℝ) ≤ ((174043092784141 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (146 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_146.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_146.trans
      change ((86973483967503 / 140737488355328 : ℚ) : ℝ) ≤ ((173946967935006 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (147 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_147.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_147.trans
      change ((86925405514113 / 140737488355328 : ℚ) : ℝ) ≤ ((173850811028226 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (148 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_148.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_148.trans
      change ((173754622047761 / 281474976710656 : ℚ) : ℝ) ≤ ((173754622047761 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (149 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_149.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_149.trans
      change ((86829200488781 / 140737488355328 : ℚ) : ℝ) ≤ ((173658400977562 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (150 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_150.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_150.trans
      change ((86781073900783 / 140737488355328 : ℚ) : ℝ) ≤ ((173562147801566 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (151 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_151.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_151.trans
      change ((173465862503703 / 281474976710656 : ℚ) : ℝ) ≤ ((173465862503703 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (152 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_152.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_152.trans
      change ((86684772533945 / 140737488355328 : ℚ) : ℝ) ≤ ((173369545067890 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (153 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_153.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_153.trans
      change ((86636597739017 / 140737488355328 : ℚ) : ℝ) ≤ ((173273195478034 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (154 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_154.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_154.trans
      change ((173176813718031 / 281474976710656 : ℚ) : ℝ) ≤ ((173176813718031 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (155 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_155.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_155.trans
      change ((173080399771767 / 281474976710656 : ℚ) : ℝ) ≤ ((173080399771767 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (156 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_156.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_156.trans
      change ((43245988405779 / 70368744177664 : ℚ) : ℝ) ≤ ((172983953623116 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (157 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_157.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_157.trans
      change ((86443737627971 / 140737488355328 : ℚ) : ℝ) ≤ ((172887475255942 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (158 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_158.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_158.trans
      change ((172790964654097 / 281474976710656 : ℚ) : ℝ) ≤ ((172790964654097 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (159 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_159.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_159.trans
      change ((86347210900713 / 140737488355328 : ℚ) : ℝ) ≤ ((172694421801426 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (160 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_160.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_160.trans
      change ((172597846681757 / 281474976710656 : ℚ) : ℝ) ≤ ((172597846681757 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (161 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_161.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_161.trans
      change ((86250619639457 / 140737488355328 : ℚ) : ℝ) ≤ ((172501239278914 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (162 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_162.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_162.trans
      change ((172404599576705 / 281474976710656 : ℚ) : ℝ) ≤ ((172404599576705 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (163 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_163.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_163.trans
      change ((172307927558929 / 281474976710656 : ℚ) : ℝ) ≤ ((172307927558929 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (164 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_164.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_164.trans
      change ((86105611604687 / 140737488355328 : ℚ) : ℝ) ≤ ((172211223209374 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (165 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_165.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_165.trans
      change ((86057243255909 / 140737488355328 : ℚ) : ℝ) ≤ ((172114486511818 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (166 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_166.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_166.trans
      change ((43004429362507 / 70368744177664 : ℚ) : ℝ) ≤ ((172017717450028 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (167 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_167.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_167.trans
      change ((85960458003879 / 140737488355328 : ℚ) : ℝ) ≤ ((171920916007758 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (168 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_168.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_168.trans
      change ((85912041084377 / 140737488355328 : ℚ) : ℝ) ≤ ((171824082168754 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (169 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_169.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_169.trans
      change ((85863607958375 / 140737488355328 : ℚ) : ℝ) ≤ ((171727215916750 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (170 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_170.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_170.trans
      change ((42907579308867 / 70368744177664 : ℚ) : ℝ) ≤ ((171630317235468 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (171 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_171.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_171.trans
      change ((171533386108621 / 281474976710656 : ℚ) : ℝ) ≤ ((171533386108621 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (172 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_172.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_172.trans
      change ((171436422519909 / 281474976710656 : ℚ) : ℝ) ≤ ((171436422519909 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (173 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_173.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_173.trans
      change ((171339426453023 / 281474976710656 : ℚ) : ℝ) ≤ ((171339426453023 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (174 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_174.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_174.trans
      change ((85621198945821 / 140737488355328 : ℚ) : ℝ) ≤ ((171242397891642 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (175 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_175.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_175.trans
      change ((171145336819435 / 281474976710656 : ℚ) : ℝ) ≤ ((171145336819435 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (176 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_176.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_176.trans
      change ((42762060805015 / 70368744177664 : ℚ) : ℝ) ≤ ((171048243220060 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (177 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_177.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_177.trans
      change ((170951117077161 / 281474976710656 : ℚ) : ℝ) ≤ ((170951117077161 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (178 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_178.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_178.trans
      change ((21356744796797 / 35184372088832 : ℚ) : ℝ) ≤ ((170853958374376 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (179 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_179.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_179.trans
      change ((5336148971729 / 8796093022208 : ℚ) : ℝ) ≤ ((170756767095328 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (180 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_180.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_180.trans
      change ((170659543223631 / 281474976710656 : ℚ) : ℝ) ≤ ((170659543223631 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (181 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_181.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_181.trans
      change ((21320285842861 / 35184372088832 : ℚ) : ℝ) ≤ ((170562286742888 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (182 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_182.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_182.trans
      change ((85232498818345 / 140737488355328 : ℚ) : ℝ) ≤ ((170464997636690 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (183 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_183.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_183.trans
      change ((85183837944309 / 140737488355328 : ℚ) : ℝ) ≤ ((170367675888618 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (184 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_184.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_184.trans
      change ((170270321482241 / 281474976710656 : ℚ) : ℝ) ≤ ((170270321482241 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (185 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_185.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_185.trans
      change ((85086467200559 / 140737488355328 : ℚ) : ℝ) ≤ ((170172934401118 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (186 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_186.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_186.trans
      change ((42518878657199 / 70368744177664 : ℚ) : ℝ) ≤ ((170075514628796 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (187 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_187.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_187.trans
      change ((169978062148811 / 281474976710656 : ℚ) : ℝ) ≤ ((169978062148811 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (188 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_188.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_188.trans
      change ((84940288472345 / 140737488355328 : ℚ) : ℝ) ≤ ((169880576944690 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (189 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_189.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_189.trans
      change ((84891529499973 / 140737488355328 : ℚ) : ℝ) ≤ ((169783058999946 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (190 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_190.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_190.trans
      change ((169685508298083 / 281474976710656 : ℚ) : ℝ) ≤ ((169685508298083 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (191 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_191.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_191.trans
      change ((2649811325353 / 4398046511104 : ℚ) : ℝ) ≤ ((169587924822592 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (192 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_192.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_192.trans
      change ((169490308556955 / 281474976710656 : ℚ) : ℝ) ≤ ((169490308556955 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (193 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_193.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_193.trans
      change ((169392659484641 / 281474976710656 : ℚ) : ℝ) ≤ ((169392659484641 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (194 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_194.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_194.trans
      change ((84647488794555 / 140737488355328 : ℚ) : ℝ) ≤ ((169294977589110 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (195 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_195.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_195.trans
      change ((169197262853809 / 281474976710656 : ℚ) : ℝ) ≤ ((169197262853809 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (196 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_196.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_196.trans
      change ((84549757631087 / 140737488355328 : ℚ) : ℝ) ≤ ((169099515262174 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (197 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_197.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_197.trans
      change ((2640652106213 / 4398046511104 : ℚ) : ℝ) ≤ ((169001734797632 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (198 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_198.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_198.trans
      change ((42225980360899 / 70368744177664 : ℚ) : ℝ) ≤ ((168903921443596 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (199 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_199.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_199.trans
      change ((84403037591735 / 140737488355328 : ℚ) : ℝ) ≤ ((168806075183470 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (200 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_200.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_200.trans
      change ((168708196000645 / 281474976710656 : ℚ) : ℝ) ≤ ((168708196000645 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (201 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_201.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_201.trans
      change ((84305141939251 / 140737488355328 : ℚ) : ℝ) ≤ ((168610283878502 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (202 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_202.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_202.trans
      change ((168512338800411 / 281474976710656 : ℚ) : ℝ) ≤ ((168512338800411 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (203 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_203.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_203.trans
      change ((84207180374865 / 140737488355328 : ℚ) : ℝ) ≤ ((168414360749730 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (204 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_204.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_204.trans
      change ((168316349709807 / 281474976710656 : ℚ) : ℝ) ≤ ((168316349709807 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (205 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_205.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_205.trans
      change ((168218305663977 / 281474976710656 : ℚ) : ℝ) ≤ ((168218305663977 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (206 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_206.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_206.trans
      change ((168120228595565 / 281474976710656 : ℚ) : ℝ) ≤ ((168120228595565 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (207 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_207.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_207.trans
      change ((42005529621971 / 70368744177664 : ℚ) : ℝ) ≤ ((168022118487884 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (208 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_208.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_208.trans
      change ((167923975324237 / 281474976710656 : ℚ) : ℝ) ≤ ((167923975324237 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (209 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_209.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_209.trans
      change ((167825799087915 / 281474976710656 : ℚ) : ℝ) ≤ ((167825799087915 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (210 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_210.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_210.trans
      change ((83863794881099 / 140737488355328 : ℚ) : ℝ) ≤ ((167727589762198 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (211 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_211.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_211.trans
      change ((83814673665177 / 140737488355328 : ℚ) : ℝ) ≤ ((167629347330354 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (212 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_212.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_212.trans
      change ((167531071775639 / 281474976710656 : ℚ) : ℝ) ≤ ((167531071775639 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (213 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_213.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_213.trans
      change ((167432763081301 / 281474976710656 : ℚ) : ℝ) ≤ ((167432763081301 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (214 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_214.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_214.trans
      change ((83667210615287 / 140737488355328 : ℚ) : ℝ) ≤ ((167334421230574 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (215 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_215.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_215.trans
      change ((20904505775835 / 35184372088832 : ℚ) : ℝ) ≤ ((167236046206680 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (216 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_216.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_216.trans
      change ((167137637992833 / 281474976710656 : ℚ) : ℝ) ≤ ((167137637992833 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (217 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_217.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_217.trans
      change ((20879899571529 / 35184372088832 : ℚ) : ℝ) ≤ ((167039196572232 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (218 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_218.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_218.trans
      change ((83470360964033 / 140737488355328 : ℚ) : ℝ) ≤ ((166940721928066 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (219 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_219.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_219.trans
      change ((166842214043515 / 281474976710656 : ℚ) : ℝ) ≤ ((166842214043515 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (220 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_220.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_220.trans
      change ((10421479556359 / 17592186044416 : ℚ) : ℝ) ≤ ((166743672901744 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (221 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_221.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_221.trans
      change ((166645098485909 / 281474976710656 : ℚ) : ℝ) ≤ ((166645098485909 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (222 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_222.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_222.trans
      change ((166546490779153 / 281474976710656 : ℚ) : ℝ) ≤ ((166546490779153 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (223 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_223.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_223.trans
      change ((650186913143 / 1099511627776 : ℚ) : ℝ) ≤ ((166447849764608 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (224 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_224.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_224.trans
      change ((166349175425397 / 281474976710656 : ℚ) : ℝ) ≤ ((166349175425397 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (225 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_225.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_225.trans
      change ((166250467744629 / 281474976710656 : ℚ) : ℝ) ≤ ((166250467744629 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (226 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_226.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_226.trans
      change ((166151726705401 / 281474976710656 : ℚ) : ℝ) ≤ ((166151726705401 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (227 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_227.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_227.trans
      change ((10378309518175 / 17592186044416 : ℚ) : ℝ) ≤ ((166052952290800 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (228 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_228.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_228.trans
      change ((165954144483903 / 281474976710656 : ℚ) : ℝ) ≤ ((165954144483903 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (229 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_229.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_229.trans
      change ((165855303267773 / 281474976710656 : ℚ) : ℝ) ≤ ((165855303267773 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (230 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_230.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_230.trans
      change ((82878214312731 / 140737488355328 : ℚ) : ℝ) ≤ ((165756428625462 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (231 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_231.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_231.trans
      change ((165657520540011 / 281474976710656 : ℚ) : ℝ) ≤ ((165657520540011 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (232 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_232.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_232.trans
      change ((82779289497225 / 140737488355328 : ℚ) : ℝ) ≤ ((165558578994450 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (233 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_233.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_233.trans
      change ((82729801985899 / 140737488355328 : ℚ) : ℝ) ≤ ((165459603971798 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (234 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_234.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_234.trans
      change ((165360595455059 / 281474976710656 : ℚ) : ℝ) ≤ ((165360595455059 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (235 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_235.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_235.trans
      change ((165261553427231 / 281474976710656 : ℚ) : ℝ) ≤ ((165261553427231 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (236 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_236.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_236.trans
      change ((165162477871295 / 281474976710656 : ℚ) : ℝ) ≤ ((165162477871295 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (237 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_237.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_237.trans
      change ((10316460548139 / 17592186044416 : ℚ) : ℝ) ≤ ((165063368770224 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (238 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_238.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_238.trans
      change ((164964226106979 / 281474976710656 : ℚ) : ℝ) ≤ ((164964226106979 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (239 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_239.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_239.trans
      change ((164865049864509 / 281474976710656 : ℚ) : ℝ) ≤ ((164865049864509 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (240 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_240.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_240.trans
      change ((82382920012875 / 140737488355328 : ℚ) : ℝ) ≤ ((164765840025750 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (241 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_241.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_241.trans
      change ((82333298286815 / 140737488355328 : ℚ) : ℝ) ≤ ((164666596573630 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (242 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_242.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_242.trans
      change ((164567319491061 / 281474976710656 : ℚ) : ℝ) ≤ ((164567319491061 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (243 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_243.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_243.trans
      change ((82234004380473 / 140737488355328 : ℚ) : ℝ) ≤ ((164468008760946 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (244 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_244.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_244.trans
      change ((82184332183089 / 140737488355328 : ℚ) : ℝ) ≤ ((164368664366178 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (245 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_245.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_245.trans
      change ((164269286289635 / 281474976710656 : ℚ) : ℝ) ≤ ((164269286289635 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (246 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_246.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_246.trans
      change ((20521234314273 / 35184372088832 : ℚ) : ℝ) ≤ ((164169874514184 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (247 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_247.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_247.trans
      change ((164070429022683 / 281474976710656 : ℚ) : ℝ) ≤ ((164070429022683 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (248 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_248.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_248.trans
      change ((20496368724747 / 35184372088832 : ℚ) : ℝ) ≤ ((163970949797976 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (249 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_249.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_249.trans
      change ((10241964801431 / 17592186044416 : ℚ) : ℝ) ≤ ((163871436822896 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (250 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_250.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_250.trans
      change ((163771890080265 / 281474976710656 : ℚ) : ℝ) ≤ ((163771890080265 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (251 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_251.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_251.trans
      change ((163672309552891 / 281474976710656 : ℚ) : ℝ) ≤ ((163672309552891 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (252 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_252.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_252.trans
      change ((40893173805893 / 70368744177664 : ℚ) : ℝ) ≤ ((163572695223572 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (253 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_253.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_253.trans
      change ((163473047075097 / 281474976710656 : ℚ) : ℝ) ≤ ((163473047075097 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (254 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_254.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_254.trans
      change ((81686682545119 / 140737488355328 : ℚ) : ℝ) ≤ ((163373365090238 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (255 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_255.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_255.trans
      change ((81636824625879 / 140737488355328 : ℚ) : ℝ) ≤ ((163273649251758 : ℕ) : ℝ) / 2^48
      norm_num
end LegendreK6.M2Pilot.FactorBounds.Sigma001
