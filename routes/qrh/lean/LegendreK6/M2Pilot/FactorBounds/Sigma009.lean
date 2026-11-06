import LegendreK6.M2Pilot.Enclosures.Sigma009
import LegendreK6.M2PilotIntegerData

/-! Join checked analytic enclosures to the exact dyadic witness table. -/
namespace LegendreK6.M2Pilot.FactorBounds.Sigma009
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem bounds (i : Fin 1536) (hlo : 1152 ≤ i.val) (hhi : i.val < 1280) :
    sigmaFactor i ≤ sigmaDyadicFactor i ∧ sigmaPower i ≤ sigmaDyadicPower i := by
  interval_cases hi : i.val
  · have heq : i = (1152 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1152.trans
      change ((73985 / 281474976710656 : ℚ) : ℝ) ≤ ((73985 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1152.trans
      change ((57738456761161 / 281474976710656 : ℚ) : ℝ) ≤ ((57738456761161 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1153 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1153.trans
      change ((76069 / 281474976710656 : ℚ) : ℝ) ≤ ((76069 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1153.trans
      change ((57599634585017 / 281474976710656 : ℚ) : ℝ) ≤ ((57599634585017 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1154 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1154.trans
      change ((19553 / 70368744177664 : ℚ) : ℝ) ≤ ((78212 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1154.trans
      change ((28730378384361 / 140737488355328 : ℚ) : ℝ) ≤ ((57460756768722 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1155 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1155.trans
      change ((80415 / 281474976710656 : ℚ) : ℝ) ≤ ((80415 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1155.trans
      change ((57321823278819 / 281474976710656 : ℚ) : ℝ) ≤ ((57321823278819 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1156 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1156.trans
      change ((82679 / 281474976710656 : ℚ) : ℝ) ≤ ((82679 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1156.trans
      change ((57182834081823 / 281474976710656 : ℚ) : ℝ) ≤ ((57182834081823 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1157 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1157.trans
      change ((85007 / 281474976710656 : ℚ) : ℝ) ≤ ((85007 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1157.trans
      change ((57043789144223 / 281474976710656 : ℚ) : ℝ) ≤ ((57043789144223 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1158 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1158.trans
      change ((10925 / 35184372088832 : ℚ) : ℝ) ≤ ((87400 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1158.trans
      change ((1778271513515 / 8796093022208 : ℚ) : ℝ) ≤ ((56904688432480 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1159 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1159.trans
      change ((89859 / 281474976710656 : ℚ) : ℝ) ≤ ((89859 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1159.trans
      change ((56765531913029 / 281474976710656 : ℚ) : ℝ) ≤ ((56765531913029 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1160 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1160.trans
      change ((92387 / 281474976710656 : ℚ) : ℝ) ≤ ((92387 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1160.trans
      change ((28313159776139 / 140737488355328 : ℚ) : ℝ) ≤ ((56626319552278 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1161 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1161.trans
      change ((94985 / 281474976710656 : ℚ) : ℝ) ≤ ((94985 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1161.trans
      change ((441305088411 / 2199023255552 : ℚ) : ℝ) ≤ ((56487051316608 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1162 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1162.trans
      change ((12207 / 35184372088832 : ℚ) : ℝ) ≤ ((97656 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1162.trans
      change ((56347727172373 / 281474976710656 : ℚ) : ℝ) ≤ ((56347727172373 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1163 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1163.trans
      change ((50201 / 140737488355328 : ℚ) : ℝ) ≤ ((100402 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1163.trans
      change ((14052086771475 / 70368744177664 : ℚ) : ℝ) ≤ ((56208347085900 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1164 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1164.trans
      change ((103223 / 281474976710656 : ℚ) : ℝ) ≤ ((103223 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1164.trans
      change ((56068911023489 / 281474976710656 : ℚ) : ℝ) ≤ ((56068911023489 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1165 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1165.trans
      change ((26531 / 70368744177664 : ℚ) : ℝ) ≤ ((106124 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1165.trans
      change ((13982354737853 / 70368744177664 : ℚ) : ℝ) ≤ ((55929418951412 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1166 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1166.trans
      change ((109105 / 281474976710656 : ℚ) : ℝ) ≤ ((109105 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1166.trans
      change ((55789870835915 / 281474976710656 : ℚ) : ℝ) ≤ ((55789870835915 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1167 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1167.trans
      change ((56085 / 140737488355328 : ℚ) : ℝ) ≤ ((112170 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1167.trans
      change ((3478141665201 / 17592186044416 : ℚ) : ℝ) ≤ ((55650266643216 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1168 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1168.trans
      change ((115319 / 281474976710656 : ℚ) : ℝ) ≤ ((115319 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1168.trans
      change ((13877651584877 / 70368744177664 : ℚ) : ℝ) ≤ ((55510606339508 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1169 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1169.trans
      change ((118557 / 281474976710656 : ℚ) : ℝ) ≤ ((118557 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1169.trans
      change ((27685444945477 / 140737488355328 : ℚ) : ℝ) ≤ ((55370889890954 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1170 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1170.trans
      change ((30471 / 70368744177664 : ℚ) : ℝ) ≤ ((121884 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1170.trans
      change ((13807779315923 / 70368744177664 : ℚ) : ℝ) ≤ ((55231117263692 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1171 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1171.trans
      change ((15663 / 35184372088832 : ℚ) : ℝ) ≤ ((125304 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1171.trans
      change ((27545644211915 / 140737488355328 : ℚ) : ℝ) ≤ ((55091288423830 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1172 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1172.trans
      change ((32205 / 70368744177664 : ℚ) : ℝ) ≤ ((128820 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1172.trans
      change ((13737850834363 / 70368744177664 : ℚ) : ℝ) ≤ ((54951403337452 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1173 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1173.trans
      change ((8277 / 17592186044416 : ℚ) : ℝ) ≤ ((132432 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1173.trans
      change ((54811461970613 / 281474976710656 : ℚ) : ℝ) ≤ ((54811461970613 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1174 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1174.trans
      change ((68073 / 140737488355328 : ℚ) : ℝ) ≤ ((136146 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1174.trans
      change ((54671464289341 / 281474976710656 : ℚ) : ℝ) ≤ ((54671464289341 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1175 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1175.trans
      change ((139963 / 281474976710656 : ℚ) : ℝ) ≤ ((139963 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1175.trans
      change ((54531410259635 / 281474976710656 : ℚ) : ℝ) ≤ ((54531410259635 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1176 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1176.trans
      change ((143885 / 281474976710656 : ℚ) : ℝ) ≤ ((143885 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1176.trans
      change ((27195649923735 / 140737488355328 : ℚ) : ℝ) ≤ ((54391299847470 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1177 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1177.trans
      change ((147917 / 281474976710656 : ℚ) : ℝ) ≤ ((147917 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1177.trans
      change ((54251133018791 / 281474976710656 : ℚ) : ℝ) ≤ ((54251133018791 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1178 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1178.trans
      change ((152061 / 281474976710656 : ℚ) : ℝ) ≤ ((152061 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1178.trans
      change ((54110909739517 / 281474976710656 : ℚ) : ℝ) ≤ ((54110909739517 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1179 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1179.trans
      change ((156319 / 281474976710656 : ℚ) : ℝ) ≤ ((156319 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1179.trans
      change ((26985314987769 / 140737488355328 : ℚ) : ℝ) ≤ ((53970629975538 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1180 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1180.trans
      change ((20087 / 35184372088832 : ℚ) : ℝ) ≤ ((160696 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1180.trans
      change ((26915146846359 / 140737488355328 : ℚ) : ℝ) ≤ ((53830293692718 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1181 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1181.trans
      change ((165195 / 281474976710656 : ℚ) : ℝ) ≤ ((165195 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1181.trans
      change ((13422475214223 / 70368744177664 : ℚ) : ℝ) ≤ ((53689900856892 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1182 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1182.trans
      change ((84909 / 140737488355328 : ℚ) : ℝ) ≤ ((169818 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1182.trans
      change ((26774725716935 / 140737488355328 : ℚ) : ℝ) ≤ ((53549451433870 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1183 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1183.trans
      change ((87285 / 140737488355328 : ℚ) : ℝ) ≤ ((174570 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1183.trans
      change ((53408945389431 / 281474976710656 : ℚ) : ℝ) ≤ ((53408945389431 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1184 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1184.trans
      change ((179453 / 281474976710656 : ℚ) : ℝ) ≤ ((179453 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1184.trans
      change ((53268382689329 / 281474976710656 : ℚ) : ℝ) ≤ ((53268382689329 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1185 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1185.trans
      change ((23059 / 35184372088832 : ℚ) : ℝ) ≤ ((184472 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1185.trans
      change ((53127763299289 / 281474976710656 : ℚ) : ℝ) ≤ ((53127763299289 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1186 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1186.trans
      change ((94815 / 140737488355328 : ℚ) : ℝ) ≤ ((189630 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1186.trans
      change ((26493543592505 / 140737488355328 : ℚ) : ℝ) ≤ ((52987087185010 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1187 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1187.trans
      change ((194931 / 281474976710656 : ℚ) : ℝ) ≤ ((194931 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1187.trans
      change ((26423177156081 / 140737488355328 : ℚ) : ℝ) ≤ ((52846354312162 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1188 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1188.trans
      change ((200379 / 281474976710656 : ℚ) : ℝ) ≤ ((200379 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1188.trans
      change ((26352782323193 / 140737488355328 : ℚ) : ℝ) ≤ ((52705564646386 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1189 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1189.trans
      change ((205977 / 281474976710656 : ℚ) : ℝ) ≤ ((205977 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1189.trans
      change ((52564718153299 / 281474976710656 : ℚ) : ℝ) ≤ ((52564718153299 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1190 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1190.trans
      change ((211731 / 281474976710656 : ℚ) : ℝ) ≤ ((211731 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1190.trans
      change ((26211907399243 / 140737488355328 : ℚ) : ℝ) ≤ ((52423814798486 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1191 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1191.trans
      change ((54411 / 70368744177664 : ℚ) : ℝ) ≤ ((217644 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1191.trans
      change ((13070713636877 / 70368744177664 : ℚ) : ℝ) ≤ ((52282854547508 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1192 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1192.trans
      change ((223721 / 281474976710656 : ℚ) : ℝ) ≤ ((223721 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1192.trans
      change ((52141837365895 / 281474976710656 : ℚ) : ℝ) ≤ ((52141837365895 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1193 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1193.trans
      change ((114983 / 140737488355328 : ℚ) : ℝ) ≤ ((229966 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1193.trans
      change ((52000763219151 / 281474976710656 : ℚ) : ℝ) ≤ ((52000763219151 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1194 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1194.trans
      change ((236383 / 281474976710656 : ℚ) : ℝ) ≤ ((236383 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1194.trans
      change ((3241227004547 / 17592186044416 : ℚ) : ℝ) ≤ ((51859632072752 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1195 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1195.trans
      change ((242979 / 281474976710656 : ℚ) : ℝ) ≤ ((242979 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1195.trans
      change ((51718443892145 / 281474976710656 : ℚ) : ℝ) ≤ ((51718443892145 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1196 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1196.trans
      change ((62439 / 70368744177664 : ℚ) : ℝ) ≤ ((249756 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1196.trans
      change ((51577198642751 / 281474976710656 : ℚ) : ℝ) ≤ ((51577198642751 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1197 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1197.trans
      change ((256721 / 281474976710656 : ℚ) : ℝ) ≤ ((256721 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1197.trans
      change ((51435896289961 / 281474976710656 : ℚ) : ℝ) ≤ ((51435896289961 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1198 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1198.trans
      change ((263879 / 281474976710656 : ℚ) : ℝ) ≤ ((263879 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1198.trans
      change ((51294536799139 / 281474976710656 : ℚ) : ℝ) ≤ ((51294536799139 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1199 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1199.trans
      change ((135617 / 140737488355328 : ℚ) : ℝ) ≤ ((271234 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1199.trans
      change ((51153120135621 / 281474976710656 : ℚ) : ℝ) ≤ ((51153120135621 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1200 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1200.trans
      change ((34849 / 35184372088832 : ℚ) : ℝ) ≤ ((278792 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1200.trans
      change ((51011646264715 / 281474976710656 : ℚ) : ℝ) ≤ ((51011646264715 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1201 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1201.trans
      change ((8955 / 8796093022208 : ℚ) : ℝ) ≤ ((286560 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1201.trans
      change ((12717528787925 / 70368744177664 : ℚ) : ℝ) ≤ ((50870115151700 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1202 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1202.trans
      change ((294541 / 281474976710656 : ℚ) : ℝ) ≤ ((294541 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1202.trans
      change ((50728526761829 / 281474976710656 : ℚ) : ℝ) ≤ ((50728526761829 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1203 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1203.trans
      change ((302743 / 281474976710656 : ℚ) : ℝ) ≤ ((302743 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1203.trans
      change ((50586881060325 / 281474976710656 : ℚ) : ℝ) ≤ ((50586881060325 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1204 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1204.trans
      change ((77793 / 70368744177664 : ℚ) : ℝ) ≤ ((311172 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1204.trans
      change ((50445178012383 / 281474976710656 : ℚ) : ℝ) ≤ ((50445178012383 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1205 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1205.trans
      change ((319833 / 281474976710656 : ℚ) : ℝ) ≤ ((319833 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1205.trans
      change ((25151708791585 / 140737488355328 : ℚ) : ℝ) ≤ ((50303417583170 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1206 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1206.trans
      change ((82183 / 70368744177664 : ℚ) : ℝ) ≤ ((328732 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1206.trans
      change ((50161599737825 / 281474976710656 : ℚ) : ℝ) ≤ ((50161599737825 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1207 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1207.trans
      change ((168939 / 140737488355328 : ℚ) : ℝ) ≤ ((337878 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1207.trans
      change ((50019724441459 / 281474976710656 : ℚ) : ℝ) ≤ ((50019724441459 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1208 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1208.trans
      change ((347275 / 281474976710656 : ℚ) : ℝ) ≤ ((347275 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1208.trans
      change ((49877791659155 / 281474976710656 : ℚ) : ℝ) ≤ ((49877791659155 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1209 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1209.trans
      change ((356931 / 281474976710656 : ℚ) : ℝ) ≤ ((356931 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1209.trans
      change ((24867900677983 / 140737488355328 : ℚ) : ℝ) ≤ ((49735801355966 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1210 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1210.trans
      change ((183427 / 140737488355328 : ℚ) : ℝ) ≤ ((366854 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1210.trans
      change ((49593753496919 / 281474976710656 : ℚ) : ℝ) ≤ ((49593753496919 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1211 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1211.trans
      change ((188525 / 140737488355328 : ℚ) : ℝ) ≤ ((377050 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1211.trans
      change ((49451648047011 / 281474976710656 : ℚ) : ℝ) ≤ ((49451648047011 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1212 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1212.trans
      change ((387527 / 281474976710656 : ℚ) : ℝ) ≤ ((387527 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1212.trans
      change ((24654742485605 / 140737488355328 : ℚ) : ℝ) ≤ ((49309484971210 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1213 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1213.trans
      change ((99573 / 70368744177664 : ℚ) : ℝ) ≤ ((398292 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1213.trans
      change ((24583632117229 / 140737488355328 : ℚ) : ℝ) ≤ ((49167264234458 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1214 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1214.trans
      change ((409353 / 281474976710656 : ℚ) : ℝ) ≤ ((409353 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1214.trans
      change ((49024985801667 / 281474976710656 : ℚ) : ℝ) ≤ ((49024985801667 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1215 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1215.trans
      change ((420719 / 281474976710656 : ℚ) : ℝ) ≤ ((420719 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1215.trans
      change ((6110331204715 / 35184372088832 : ℚ) : ℝ) ≤ ((48882649637720 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1216 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1216.trans
      change ((216199 / 140737488355328 : ℚ) : ℝ) ≤ ((432398 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1216.trans
      change ((48740255707473 / 281474976710656 : ℚ) : ℝ) ≤ ((48740255707473 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1217 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1217.trans
      change ((222199 / 140737488355328 : ℚ) : ℝ) ≤ ((444398 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1217.trans
      change ((48597803975753 / 281474976710656 : ℚ) : ℝ) ≤ ((48597803975753 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1218 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1218.trans
      change ((57091 / 35184372088832 : ℚ) : ℝ) ≤ ((456728 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1218.trans
      change ((48455294407357 / 281474976710656 : ℚ) : ℝ) ≤ ((48455294407357 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1219 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1219.trans
      change ((469397 / 281474976710656 : ℚ) : ℝ) ≤ ((469397 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1219.trans
      change ((48312726967055 / 281474976710656 : ℚ) : ℝ) ≤ ((48312726967055 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1220 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1220.trans
      change ((241207 / 140737488355328 : ℚ) : ℝ) ≤ ((482414 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1220.trans
      change ((48170101619587 / 281474976710656 : ℚ) : ℝ) ≤ ((48170101619587 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1221 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1221.trans
      change ((495789 / 281474976710656 : ℚ) : ℝ) ≤ ((495789 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1221.trans
      change ((12006854582417 / 70368744177664 : ℚ) : ℝ) ≤ ((48027418329668 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1222 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1222.trans
      change ((127383 / 70368744177664 : ℚ) : ℝ) ≤ ((509532 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1222.trans
      change ((47884677061979 / 281474976710656 : ℚ) : ℝ) ≤ ((47884677061979 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1223 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1223.trans
      change ((523651 / 281474976710656 : ℚ) : ℝ) ≤ ((523651 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1223.trans
      change ((47741877781175 / 281474976710656 : ℚ) : ℝ) ≤ ((47741877781175 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1224 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1224.trans
      change ((538159 / 281474976710656 : ℚ) : ℝ) ≤ ((538159 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1224.trans
      change ((11899755112971 / 70368744177664 : ℚ) : ℝ) ≤ ((47599020451884 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1225 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1225.trans
      change ((553065 / 281474976710656 : ℚ) : ℝ) ≤ ((553065 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1225.trans
      change ((23728052519351 / 140737488355328 : ℚ) : ℝ) ≤ ((47456105038702 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1226 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1226.trans
      change ((142095 / 70368744177664 : ℚ) : ℝ) ≤ ((568380 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1226.trans
      change ((47313131506197 / 281474976710656 : ℚ) : ℝ) ≤ ((47313131506197 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1227 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1227.trans
      change ((584115 / 281474976710656 : ℚ) : ℝ) ≤ ((584115 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1227.trans
      change ((47170099818911 / 281474976710656 : ℚ) : ℝ) ≤ ((47170099818911 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1228 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1228.trans
      change ((600281 / 281474976710656 : ℚ) : ℝ) ≤ ((600281 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1228.trans
      change ((5878376242669 / 35184372088832 : ℚ) : ℝ) ≤ ((47027009941352 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1229 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1229.trans
      change ((616891 / 281474976710656 : ℚ) : ℝ) ≤ ((616891 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1229.trans
      change ((46883861838005 / 281474976710656 : ℚ) : ℝ) ≤ ((46883861838005 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1230 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1230.trans
      change ((633957 / 281474976710656 : ℚ) : ℝ) ≤ ((633957 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1230.trans
      change ((46740655473321 / 281474976710656 : ℚ) : ℝ) ≤ ((46740655473321 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1231 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1231.trans
      change ((325745 / 140737488355328 : ℚ) : ℝ) ≤ ((651490 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1231.trans
      change ((46597390811725 / 281474976710656 : ℚ) : ℝ) ≤ ((46597390811725 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1232 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1232.trans
      change ((10461 / 4398046511104 : ℚ) : ℝ) ≤ ((669504 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1232.trans
      change ((46454067817611 / 281474976710656 : ℚ) : ℝ) ≤ ((46454067817611 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1233 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1233.trans
      change ((688011 / 281474976710656 : ℚ) : ℝ) ≤ ((688011 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1233.trans
      change ((11577671613837 / 70368744177664 : ℚ) : ℝ) ≤ ((46310686455348 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1234 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1234.trans
      change ((707025 / 281474976710656 : ℚ) : ℝ) ≤ ((707025 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1234.trans
      change ((23083623344635 / 140737488355328 : ℚ) : ℝ) ≤ ((46167246689270 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1235 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1235.trans
      change ((22705 / 8796093022208 : ℚ) : ℝ) ≤ ((726560 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1235.trans
      change ((5752968560461 / 35184372088832 : ℚ) : ℝ) ≤ ((46023748483688 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1236 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1236.trans
      change ((746629 / 281474976710656 : ℚ) : ℝ) ≤ ((746629 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1236.trans
      change ((22940095901439 / 140737488355328 : ℚ) : ℝ) ≤ ((45880191802878 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1237 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1237.trans
      change ((47953 / 17592186044416 : ℚ) : ℝ) ≤ ((767248 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1237.trans
      change ((45736576611093 / 281474976710656 : ℚ) : ℝ) ≤ ((45736576611093 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1238 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1238.trans
      change ((394215 / 140737488355328 : ℚ) : ℝ) ≤ ((788430 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1238.trans
      change ((45592902872551 / 281474976710656 : ℚ) : ℝ) ≤ ((45592902872551 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1239 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1239.trans
      change ((810193 / 281474976710656 : ℚ) : ℝ) ≤ ((810193 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1239.trans
      change ((22724585275723 / 140737488355328 : ℚ) : ℝ) ≤ ((45449170551446 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1240 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1240.trans
      change ((416275 / 140737488355328 : ℚ) : ℝ) ≤ ((832550 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1240.trans
      change ((45305379611939 / 281474976710656 : ℚ) : ℝ) ≤ ((45305379611939 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1241 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1241.trans
      change ((427759 / 140737488355328 : ℚ) : ℝ) ≤ ((855518 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1241.trans
      change ((45161530018163 / 281474976710656 : ℚ) : ℝ) ≤ ((45161530018163 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1242 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1242.trans
      change ((879115 / 281474976710656 : ℚ) : ℝ) ≤ ((879115 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1242.trans
      change ((22508810867111 / 140737488355328 : ℚ) : ℝ) ≤ ((45017621734222 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1243 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1243.trans
      change ((225839 / 70368744177664 : ℚ) : ℝ) ≤ ((903356 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1243.trans
      change ((44873654724191 / 281474976710656 : ℚ) : ℝ) ≤ ((44873654724191 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1244 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1244.trans
      change ((928259 / 281474976710656 : ℚ) : ℝ) ≤ ((928259 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1244.trans
      change ((11182407238029 / 70368744177664 : ℚ) : ℝ) ≤ ((44729628952116 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1245 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1245.trans
      change ((476921 / 140737488355328 : ℚ) : ℝ) ≤ ((953842 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1245.trans
      change ((44585544382011 / 281474976710656 : ℚ) : ℝ) ≤ ((44585544382011 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1246 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1246.trans
      change ((245031 / 70368744177664 : ℚ) : ℝ) ≤ ((980124 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1246.trans
      change ((5555175122233 / 35184372088832 : ℚ) : ℝ) ≤ ((44441400977864 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1247 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1247.trans
      change ((1007123 / 281474976710656 : ℚ) : ℝ) ≤ ((1007123 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1247.trans
      change ((44297198703631 / 281474976710656 : ℚ) : ℝ) ≤ ((44297198703631 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1248 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1248.trans
      change ((1034859 / 281474976710656 : ℚ) : ℝ) ≤ ((1034859 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1248.trans
      change ((44152937523241 / 281474976710656 : ℚ) : ℝ) ≤ ((44152937523241 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1249 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1249.trans
      change ((132919 / 35184372088832 : ℚ) : ℝ) ≤ ((1063352 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1249.trans
      change ((44008617400591 / 281474976710656 : ℚ) : ℝ) ≤ ((44008617400591 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1250 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1250.trans
      change ((546311 / 140737488355328 : ℚ) : ℝ) ≤ ((1092622 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1250.trans
      change ((21932119149775 / 140737488355328 : ℚ) : ℝ) ≤ ((43864238299550 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1251 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1251.trans
      change ((561345 / 140737488355328 : ℚ) : ℝ) ≤ ((1122690 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1251.trans
      change ((43719800183957 / 281474976710656 : ℚ) : ℝ) ≤ ((43719800183957 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1252 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1252.trans
      change ((576789 / 140737488355328 : ℚ) : ℝ) ≤ ((1153578 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1252.trans
      change ((21787651508811 / 140737488355328 : ℚ) : ℝ) ≤ ((43575303017622 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1253 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1253.trans
      change ((1185307 / 281474976710656 : ℚ) : ℝ) ≤ ((1185307 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1253.trans
      change ((10857686691081 / 70368744177664 : ℚ) : ℝ) ≤ ((43430746764324 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1254 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1254.trans
      change ((1217901 / 281474976710656 : ℚ) : ℝ) ≤ ((1217901 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1254.trans
      change ((43286131387815 / 281474976710656 : ℚ) : ℝ) ≤ ((43286131387815 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1255 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1255.trans
      change ((1251383 / 281474976710656 : ℚ) : ℝ) ≤ ((1251383 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1255.trans
      change ((21570728425907 / 140737488355328 : ℚ) : ℝ) ≤ ((43141456851814 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1256 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1256.trans
      change ((80361 / 17592186044416 : ℚ) : ℝ) ≤ ((1285776 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1256.trans
      change ((42996723120013 / 281474976710656 : ℚ) : ℝ) ≤ ((42996723120013 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1257 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1257.trans
      change ((660553 / 140737488355328 : ℚ) : ℝ) ≤ ((1321106 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1257.trans
      change ((42851930156073 / 281474976710656 : ℚ) : ℝ) ≤ ((42851930156073 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1258 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1258.trans
      change ((678699 / 140737488355328 : ℚ) : ℝ) ≤ ((1357398 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1258.trans
      change ((21353538961813 / 140737488355328 : ℚ) : ℝ) ≤ ((42707077923626 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1259 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1259.trans
      change ((348669 / 70368744177664 : ℚ) : ℝ) ≤ ((1394676 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1259.trans
      change ((1330067699571 / 8796093022208 : ℚ) : ℝ) ≤ ((42562166386272 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1260 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1260.trans
      change ((716485 / 140737488355328 : ℚ) : ℝ) ≤ ((1432970 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1260.trans
      change ((42417195507585 / 281474976710656 : ℚ) : ℝ) ≤ ((42417195507585 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1261 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1261.trans
      change ((92019 / 17592186044416 : ℚ) : ℝ) ≤ ((1472304 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1261.trans
      change ((21136082625553 / 140737488355328 : ℚ) : ℝ) ≤ ((42272165251106 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1262 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1262.trans
      change ((378177 / 70368744177664 : ℚ) : ℝ) ≤ ((1512708 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1262.trans
      change ((42127075580347 / 281474976710656 : ℚ) : ℝ) ≤ ((42127075580347 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1263 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1263.trans
      change ((777105 / 140737488355328 : ℚ) : ℝ) ≤ ((1554210 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1263.trans
      change ((41981926458791 / 281474976710656 : ℚ) : ℝ) ≤ ((41981926458791 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1264 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1264.trans
      change ((199605 / 35184372088832 : ℚ) : ℝ) ≤ ((1596840 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1264.trans
      change ((20918358924945 / 140737488355328 : ℚ) : ℝ) ≤ ((41836717849890 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1265 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1265.trans
      change ((410157 / 70368744177664 : ℚ) : ℝ) ≤ ((1640628 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1265.trans
      change ((41691449717067 / 281474976710656 : ℚ) : ℝ) ≤ ((41691449717067 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1266 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1266.trans
      change ((842803 / 140737488355328 : ℚ) : ℝ) ≤ ((1685606 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1266.trans
      change ((20773061011857 / 140737488355328 : ℚ) : ℝ) ≤ ((41546122023714 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1267 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1267.trans
      change ((432951 / 70368744177664 : ℚ) : ℝ) ≤ ((1731804 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1267.trans
      change ((5175091841649 / 35184372088832 : ℚ) : ℝ) ≤ ((41400734733192 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1268 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1268.trans
      change ((1779257 / 281474976710656 : ℚ) : ℝ) ≤ ((1779257 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1268.trans
      change ((10313821952209 / 70368744177664 : ℚ) : ℝ) ≤ ((41255287808836 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1269 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1269.trans
      change ((1827997 / 281474976710656 : ℚ) : ℝ) ≤ ((1827997 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1269.trans
      change ((41109781213947 / 281474976710656 : ℚ) : ℝ) ≤ ((41109781213947 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1270 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1270.trans
      change ((469515 / 70368744177664 : ℚ) : ℝ) ≤ ((1878060 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1270.trans
      change ((10241053727949 / 70368744177664 : ℚ) : ℝ) ≤ ((40964214911796 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1271 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1271.trans
      change ((1929481 / 281474976710656 : ℚ) : ℝ) ≤ ((1929481 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1271.trans
      change ((40818588865627 / 281474976710656 : ℚ) : ℝ) ≤ ((40818588865627 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1272 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1272.trans
      change ((247787 / 35184372088832 : ℚ) : ℝ) ≤ ((1982296 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1272.trans
      change ((20336451519325 / 140737488355328 : ℚ) : ℝ) ≤ ((40672903038650 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1273 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1273.trans
      change ((2036543 / 281474976710656 : ℚ) : ℝ) ≤ ((2036543 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1273.trans
      change ((316618417141 / 2199023255552 : ℚ) : ℝ) ≤ ((40527157394048 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1274 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1274.trans
      change ((523065 / 70368744177664 : ℚ) : ℝ) ≤ ((2092260 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1274.trans
      change ((10095337973743 / 70368744177664 : ℚ) : ℝ) ≤ ((40381351894972 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1275 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1275.trans
      change ((2149487 / 281474976710656 : ℚ) : ℝ) ≤ ((2149487 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1275.trans
      change ((40235486504543 / 281474976710656 : ℚ) : ℝ) ≤ ((40235486504543 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1276 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1276.trans
      change ((276033 / 35184372088832 : ℚ) : ℝ) ≤ ((2208264 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1276.trans
      change ((40089561185851 / 281474976710656 : ℚ) : ℝ) ≤ ((40089561185851 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1277 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1277.trans
      change ((2268633 / 281474976710656 : ℚ) : ℝ) ≤ ((2268633 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1277.trans
      change ((19971787950979 / 140737488355328 : ℚ) : ℝ) ≤ ((39943575901958 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1278 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1278.trans
      change ((582659 / 70368744177664 : ℚ) : ℝ) ≤ ((2330636 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1278.trans
      change ((39797530615893 / 281474976710656 : ℚ) : ℝ) ≤ ((39797530615893 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1279 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma009.sigma_factor_upper_1279.trans
      change ((2394317 / 281474976710656 : ℚ) : ℝ) ≤ ((2394317 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma009.sigma_power_upper_1279.trans
      change ((39651425290655 / 281474976710656 : ℚ) : ℝ) ≤ ((39651425290655 : ℕ) : ℝ) / 2^48
      norm_num
end LegendreK6.M2Pilot.FactorBounds.Sigma009
