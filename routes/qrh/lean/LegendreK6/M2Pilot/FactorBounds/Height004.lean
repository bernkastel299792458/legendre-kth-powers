import LegendreK6.M2Pilot.Enclosures.Height004
import LegendreK6.M2PilotIntegerData

/-! Join checked analytic enclosures to the exact dyadic witness table. -/
namespace LegendreK6.M2Pilot.FactorBounds.Height004
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem bounds (i : Fin 988) (hlo : 128 ≤ i.val) (hhi : i.val < 160) :
    heightFactor i ≤ heightDyadicFactor i ∧ heightPower i ≤ heightDyadicPower i := by
  interval_cases hi : i.val
  · have heq : i = (128 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height004.height_factor_upper_128.trans
      change ((2231297320119583 / 281474976710656 : ℚ) : ℝ) ≤ ((2231297320119583 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height004.height_power_upper_128.trans
      change ((72744770803991 / 35184372088832 : ℚ) : ℝ) ≤ ((581958166431928 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (129 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height004.height_factor_upper_129.trans
      change ((276348949657151 / 35184372088832 : ℚ) : ℝ) ≤ ((2210791597257208 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height004.height_power_upper_129.trans
      change ((36656191086875 / 17592186044416 : ℚ) : ℝ) ≤ ((586499057390000 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (130 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height004.height_factor_upper_130.trans
      change ((2190473007257643 / 281474976710656 : ℚ) : ℝ) ≤ ((2190473007257643 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height004.height_power_upper_130.trans
      change ((591039875893367 / 281474976710656 : ℚ) : ℝ) ≤ ((591039875893367 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (131 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height004.height_factor_upper_131.trans
      change ((1085169927933685 / 140737488355328 : ℚ) : ℝ) ≤ ((2170339855867370 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height004.height_power_upper_131.trans
      change ((148895155503873 / 70368744177664 : ℚ) : ℝ) ≤ ((595580622015492 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (132 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height004.height_factor_upper_132.trans
      change ((1075195232016805 / 140737488355328 : ℚ) : ℝ) ≤ ((2150390464033610 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height004.height_power_upper_132.trans
      change ((600121295829729 / 281474976710656 : ℚ) : ℝ) ≤ ((600121295829729 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (133 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height004.height_factor_upper_133.trans
      change ((1065311583884685 / 140737488355328 : ℚ) : ℝ) ≤ ((2130623167769370 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height004.height_power_upper_133.trans
      change ((75582737176165 / 35184372088832 : ℚ) : ℝ) ≤ ((604661897409320 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (134 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height004.height_factor_upper_134.trans
      change ((2111036318019667 / 281474976710656 : ℚ) : ℝ) ≤ ((2111036318019667 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height004.height_power_upper_134.trans
      change ((609202426827395 / 281474976710656 : ℚ) : ℝ) ≤ ((609202426827395 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (135 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height004.height_factor_upper_135.trans
      change ((2091628280528933 / 281474976710656 : ℚ) : ℝ) ≤ ((2091628280528933 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height004.height_power_upper_135.trans
      change ((613742884156973 / 281474976710656 : ℚ) : ℝ) ≤ ((613742884156973 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (136 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height004.height_factor_upper_136.trans
      change ((2072397435709577 / 281474976710656 : ℚ) : ℝ) ≤ ((2072397435709577 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height004.height_power_upper_136.trans
      change ((154570817367741 / 70368744177664 : ℚ) : ℝ) ≤ ((618283269470964 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (137 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height004.height_factor_upper_137.trans
      change ((1026671089255851 / 140737488355328 : ℚ) : ℝ) ≤ ((2053342178511702 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height004.height_power_upper_137.trans
      change ((311411791421083 / 140737488355328 : ℚ) : ℝ) ≤ ((622823582842166 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (138 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height004.height_factor_upper_138.trans
      change ((1017230459146983 / 140737488355328 : ℚ) : ℝ) ≤ ((2034460918293966 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height004.height_power_upper_138.trans
      change ((313681912171633 / 140737488355328 : ℚ) : ℝ) ≤ ((627363824343266 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (139 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height004.height_factor_upper_139.trans
      change ((2015752078695577 / 281474976710656 : ℚ) : ℝ) ≤ ((2015752078695577 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height004.height_power_upper_139.trans
      change ((315951997023421 / 140737488355328 : ℚ) : ℝ) ≤ ((631903994046842 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (140 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height004.height_factor_upper_140.trans
      change ((1997214097509407 / 281474976710656 : ℚ) : ℝ) ≤ ((1997214097509407 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height004.height_power_upper_140.trans
      change ((318222046012681 / 140737488355328 : ℚ) : ℝ) ≤ ((636444092025362 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (141 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height004.height_factor_upper_141.trans
      change ((989422713278113 / 140737488355328 : ℚ) : ℝ) ≤ ((1978845426556226 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height004.height_power_upper_141.trans
      change ((40061507396949 / 17592186044416 : ℚ) : ℝ) ≤ ((640984118351184 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (142 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height004.height_factor_upper_142.trans
      change ((1960644531560037 / 281474976710656 : ℚ) : ℝ) ≤ ((1960644531560037 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height004.height_power_upper_142.trans
      change ((645524073096557 / 281474976710656 : ℚ) : ℝ) ≤ ((645524073096557 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (143 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height004.height_factor_upper_143.trans
      change ((971304946012251 / 140737488355328 : ℚ) : ℝ) ≤ ((1942609892024502 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height004.height_power_upper_143.trans
      change ((162515989083405 / 70368744177664 : ℚ) : ℝ) ≤ ((650063956333620 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (144 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height004.height_factor_upper_144.trans
      change ((481185000277615 / 70368744177664 : ℚ) : ℝ) ≤ ((1924740001110460 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height004.height_power_upper_144.trans
      change ((654603768134405 / 281474976710656 : ℚ) : ℝ) ≤ ((654603768134405 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (145 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height004.height_factor_upper_145.trans
      change ((953516682757257 / 140737488355328 : ℚ) : ℝ) ≤ ((1907033365514514 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height004.height_power_upper_145.trans
      change ((41196469285677 / 17592186044416 : ℚ) : ℝ) ≤ ((659143508570832 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (146 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height004.height_factor_upper_146.trans
      change ((944744252674345 / 140737488355328 : ℚ) : ℝ) ≤ ((1889488505348690 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height004.height_power_upper_146.trans
      change ((663683177714715 / 281474976710656 : ℚ) : ℝ) ≤ ((663683177714715 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (147 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height004.height_factor_upper_147.trans
      change ((58503248563161 / 8796093022208 : ℚ) : ℝ) ≤ ((1872103954021152 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height004.height_power_upper_147.trans
      change ((668222775637759 / 281474976710656 : ℚ) : ℝ) ≤ ((668222775637759 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (148 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height004.height_factor_upper_148.trans
      change ((1854878258117959 / 281474976710656 : ℚ) : ℝ) ≤ ((1854878258117959 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height004.height_power_upper_148.trans
      change ((672762302411561 / 281474976710656 : ℚ) : ℝ) ≤ ((672762302411561 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (149 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height004.height_factor_upper_149.trans
      change ((1837809977285867 / 281474976710656 : ℚ) : ℝ) ≤ ((1837809977285867 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height004.height_power_upper_149.trans
      change ((677301758107609 / 281474976710656 : ℚ) : ℝ) ≤ ((677301758107609 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (150 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height004.height_factor_upper_150.trans
      change ((1820897684116163 / 281474976710656 : ℚ) : ℝ) ≤ ((1820897684116163 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height004.height_power_upper_150.trans
      change ((170460285699321 / 70368744177664 : ℚ) : ℝ) ≤ ((681841142797284 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (151 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height004.height_factor_upper_151.trans
      change ((225517495503689 / 35184372088832 : ℚ) : ℝ) ≤ ((1804139964029512 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height004.height_power_upper_151.trans
      change ((686380456551861 / 281474976710656 : ℚ) : ℝ) ≤ ((686380456551861 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (152 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height004.height_factor_upper_152.trans
      change ((1787535415161823 / 281474976710656 : ℚ) : ℝ) ≤ ((1787535415161823 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height004.height_power_upper_152.trans
      change ((690919699442505 / 281474976710656 : ℚ) : ℝ) ≤ ((690919699442505 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (153 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height004.height_factor_upper_153.trans
      change ((221385331031389 / 35184372088832 : ℚ) : ℝ) ≤ ((1771082648251112 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height004.height_power_upper_153.trans
      change ((173864717885069 / 70368744177664 : ℚ) : ℝ) ≤ ((695458871540276 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (154 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height004.height_factor_upper_154.trans
      change ((1754780286525369 / 281474976710656 : ℚ) : ℝ) ≤ ((1754780286525369 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height004.height_power_upper_154.trans
      change ((349998986458063 / 140737488355328 : ℚ) : ℝ) ≤ ((699997972916126 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (155 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height004.height_factor_upper_155.trans
      change ((1738626965591401 / 281474976710656 : ℚ) : ℝ) ≤ ((1738626965591401 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height004.height_power_upper_155.trans
      change ((704537003640901 / 281474976710656 : ℚ) : ℝ) ≤ ((704537003640901 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (156 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height004.height_factor_upper_156.trans
      change ((861310666662331 / 140737488355328 : ℚ) : ℝ) ≤ ((1722621333324662 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height004.height_power_upper_156.trans
      change ((354537981892671 / 140737488355328 : ℚ) : ℝ) ≤ ((709075963785342 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (157 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height004.height_factor_upper_157.trans
      change ((853381024880019 / 140737488355328 : ℚ) : ℝ) ≤ ((1706762049760038 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height004.height_power_upper_157.trans
      change ((44600928338755 / 17592186044416 : ℚ) : ℝ) ≤ ((713614853420080 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (158 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height004.height_factor_upper_158.trans
      change ((422761946745903 / 70368744177664 : ℚ) : ℝ) ≤ ((1691047786983612 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height004.height_power_upper_158.trans
      change ((179538418153911 / 70368744177664 : ℚ) : ℝ) ≤ ((718153672615644 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (159 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height004.height_factor_upper_159.trans
      change ((418869307256341 / 70368744177664 : ℚ) : ℝ) ≤ ((1675477229025364 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height004.height_power_upper_159.trans
      change ((722692421442455 / 281474976710656 : ℚ) : ℝ) ≤ ((722692421442455 : ℕ) : ℝ) / 2^48
      norm_num
end LegendreK6.M2Pilot.FactorBounds.Height004
