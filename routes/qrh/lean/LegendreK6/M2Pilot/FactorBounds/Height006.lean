import LegendreK6.M2Pilot.Enclosures.Height006
import LegendreK6.M2PilotIntegerData

/-! Join checked analytic enclosures to the exact dyadic witness table. -/
namespace LegendreK6.M2Pilot.FactorBounds.Height006
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem bounds (i : Fin 988) (hlo : 192 ≤ i.val) (hhi : i.val < 224) :
    heightFactor i ≤ heightDyadicFactor i ∧ heightPower i ≤ heightDyadicPower i := by
  interval_cases hi : i.val
  · have heq : i = (192 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height006.height_factor_upper_192.trans
      change ((1234313488321509 / 281474976710656 : ℚ) : ℝ) ≤ ((1234313488321509 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height006.height_power_upper_192.trans
      change ((218108027656715 / 70368744177664 : ℚ) : ℝ) ≤ ((872432110626860 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (193 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height006.height_factor_upper_193.trans
      change ((1222924537367267 / 281474976710656 : ℚ) : ℝ) ≤ ((1222924537367267 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height006.height_power_upper_193.trans
      change ((876968508075481 / 281474976710656 : ℚ) : ℝ) ≤ ((876968508075481 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (194 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height006.height_factor_upper_194.trans
      change ((1211639989026381 / 281474976710656 : ℚ) : ℝ) ≤ ((1211639989026381 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height006.height_power_upper_194.trans
      change ((110188104694385 / 35184372088832 : ℚ) : ℝ) ≤ ((881504837555080 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (195 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height006.height_factor_upper_195.trans
      change ((600229446622315 / 140737488355328 : ℚ) : ℝ) ≤ ((1200458893244630 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height006.height_power_upper_195.trans
      change ((886041099132409 / 281474976710656 : ℚ) : ℝ) ≤ ((886041099132409 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (196 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height006.height_factor_upper_196.trans
      change ((148672538567659 / 35184372088832 : ℚ) : ℝ) ≤ ((1189380308541272 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height006.height_power_upper_196.trans
      change ((890577292874119 / 281474976710656 : ℚ) : ℝ) ≤ ((890577292874119 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (197 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height006.height_factor_upper_197.trans
      change ((1178403301932413 / 281474976710656 : ℚ) : ℝ) ≤ ((1178403301932413 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height006.height_power_upper_197.trans
      change ((447556709423383 / 140737488355328 : ℚ) : ℝ) ≤ ((895113418846766 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (198 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height006.height_factor_upper_198.trans
      change ((1167526948855061 / 281474976710656 : ℚ) : ℝ) ≤ ((1167526948855061 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height006.height_power_upper_198.trans
      change ((449824738558403 / 140737488355328 : ℚ) : ℝ) ≤ ((899649477116806 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (199 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height006.height_factor_upper_199.trans
      change ((289187583272959 / 70368744177664 : ℚ) : ℝ) ≤ ((1156750333091836 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height006.height_power_upper_199.trans
      change ((452092733875299 / 140737488355328 : ℚ) : ℝ) ≤ ((904185467750598 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (200 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height006.height_factor_upper_200.trans
      change ((573036273348181 / 140737488355328 : ℚ) : ℝ) ≤ ((1146072546696362 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height006.height_power_upper_200.trans
      change ((908721390814403 / 281474976710656 : ℚ) : ℝ) ≤ ((908721390814403 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (201 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height006.height_factor_upper_201.trans
      change ((567746344959653 / 140737488355328 : ℚ) : ℝ) ≤ ((1135492689919306 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height006.height_power_upper_201.trans
      change ((913257246374385 / 281474976710656 : ℚ) : ℝ) ≤ ((913257246374385 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (202 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height006.height_factor_upper_202.trans
      change ((562504935567541 / 140737488355328 : ℚ) : ℝ) ≤ ((1125009871135082 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height006.height_power_upper_202.trans
      change ((917793034496611 / 281474976710656 : ℚ) : ℝ) ≤ ((917793034496611 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (203 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height006.height_factor_upper_203.trans
      change ((1114623206769191 / 281474976710656 : ℚ) : ℝ) ≤ ((1114623206769191 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height006.height_power_upper_203.trans
      change ((461164377623525 / 140737488355328 : ℚ) : ℝ) ≤ ((922328755247050 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (204 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height006.height_factor_upper_204.trans
      change ((1104331821226215 / 281474976710656 : ℚ) : ℝ) ≤ ((1104331821226215 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height006.height_power_upper_204.trans
      change ((926864408691577 / 281474976710656 : ℚ) : ℝ) ≤ ((926864408691577 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (205 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height006.height_factor_upper_205.trans
      change ((547067423409221 / 140737488355328 : ℚ) : ℝ) ≤ ((1094134846818442 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height006.height_power_upper_205.trans
      change ((29106249840499 / 8796093022208 : ℚ) : ℝ) ≤ ((931399994895968 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (206 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height006.height_factor_upper_206.trans
      change ((1084031423695121 / 281474976710656 : ℚ) : ℝ) ≤ ((1084031423695121 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height006.height_power_upper_206.trans
      change ((935935513925903 / 281474976710656 : ℚ) : ℝ) ≤ ((935935513925903 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (207 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height006.height_factor_upper_207.trans
      change ((1074020699772351 / 281474976710656 : ℚ) : ℝ) ≤ ((1074020699772351 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height006.height_power_upper_207.trans
      change ((470235482923483 / 140737488355328 : ℚ) : ℝ) ≤ ((940470965846966 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (208 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height006.height_factor_upper_208.trans
      change ((266025457665895 / 70368744177664 : ℚ) : ℝ) ≤ ((1064101830663580 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height006.height_power_upper_208.trans
      change ((236251587681161 / 70368744177664 : ℚ) : ℝ) ≤ ((945006350724644 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (209 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height006.height_factor_upper_209.trans
      change ((1054273979610725 / 281474976710656 : ℚ) : ℝ) ≤ ((1054273979610725 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height006.height_power_upper_209.trans
      change ((949541668624331 / 281474976710656 : ℚ) : ℝ) ≤ ((949541668624331 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (210 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height006.height_factor_upper_210.trans
      change ((32641759919247 / 8796093022208 : ℚ) : ℝ) ≤ ((1044536317415904 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height006.height_power_upper_210.trans
      change ((954076919611323 / 281474976710656 : ℚ) : ℝ) ≤ ((954076919611323 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (211 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height006.height_factor_upper_211.trans
      change ((258722005593441 / 70368744177664 : ℚ) : ℝ) ≤ ((1034888022373764 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height006.height_power_upper_211.trans
      change ((958612103750821 / 281474976710656 : ℚ) : ℝ) ≤ ((958612103750821 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (212 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height006.height_factor_upper_212.trans
      change ((512664140102209 / 140737488355328 : ℚ) : ℝ) ≤ ((1025328280204418 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height006.height_power_upper_212.trans
      change ((963147221107931 / 281474976710656 : ℚ) : ℝ) ≤ ((963147221107931 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (213 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height006.height_factor_upper_213.trans
      change ((1015856283986967 / 281474976710656 : ℚ) : ℝ) ≤ ((1015856283986967 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height006.height_power_upper_213.trans
      change ((60480141984229 / 17592186044416 : ℚ) : ℝ) ≤ ((967682271747664 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (214 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height006.height_factor_upper_214.trans
      change ((1006471234093617 / 281474976710656 : ℚ) : ℝ) ≤ ((1006471234093617 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height006.height_power_upper_214.trans
      change ((972217255734935 / 281474976710656 : ℚ) : ℝ) ≤ ((972217255734935 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (215 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height006.height_factor_upper_215.trans
      change ((124646542265547 / 35184372088832 : ℚ) : ℝ) ≤ ((997172338124376 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height006.height_power_upper_215.trans
      change ((976752173134567 / 281474976710656 : ℚ) : ℝ) ≤ ((976752173134567 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (216 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height006.height_factor_upper_216.trans
      change ((987958810842333 / 281474976710656 : ℚ) : ℝ) ≤ ((987958810842333 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height006.height_power_upper_216.trans
      change ((981287024011285 / 281474976710656 : ℚ) : ℝ) ≤ ((981287024011285 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (217 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height006.height_factor_upper_217.trans
      change ((489414937054751 / 140737488355328 : ℚ) : ℝ) ≤ ((978829874109502 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height006.height_power_upper_217.trans
      change ((985821808429723 / 281474976710656 : ℚ) : ℝ) ≤ ((985821808429723 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (218 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height006.height_factor_upper_218.trans
      change ((484892378411623 / 140737488355328 : ℚ) : ℝ) ≤ ((969784756823246 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height006.height_power_upper_218.trans
      change ((495178263227209 / 140737488355328 : ℚ) : ℝ) ≤ ((990356526454418 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (219 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height006.height_factor_upper_219.trans
      change ((1123392927910383 / 281474976710656 : ℚ) : ℝ) ≤ ((1123392927910383 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height006.height_power_upper_219.trans
      change ((994891178149815 / 281474976710656 : ℚ) : ℝ) ≤ ((994891178149815 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (220 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height006.height_factor_upper_220.trans
      change ((1884093781574389 / 281474976710656 : ℚ) : ℝ) ≤ ((1884093781574389 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height006.height_power_upper_220.trans
      change ((124928220447533 / 35184372088832 : ℚ) : ℝ) ≤ ((999425763580264 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (221 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height006.height_factor_upper_221.trans
      change ((1837740079919619 / 281474976710656 : ℚ) : ℝ) ≤ ((1837740079919619 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height006.height_power_upper_221.trans
      change ((501980141405011 / 140737488355328 : ℚ) : ℝ) ≤ ((1003960282810022 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (222 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height006.height_factor_upper_222.trans
      change ((1792525819454725 / 281474976710656 : ℚ) : ℝ) ≤ ((1792525819454725 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height006.height_power_upper_222.trans
      change ((1008494735903253 / 281474976710656 : ℚ) : ℝ) ≤ ((1008494735903253 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (223 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height006.height_factor_upper_223.trans
      change ((1748423016192647 / 281474976710656 : ℚ) : ℝ) ≤ ((1748423016192647 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height006.height_power_upper_223.trans
      change ((1013029122924027 / 281474976710656 : ℚ) : ℝ) ≤ ((1013029122924027 : ℕ) : ℝ) / 2^48
      norm_num
end LegendreK6.M2Pilot.FactorBounds.Height006
