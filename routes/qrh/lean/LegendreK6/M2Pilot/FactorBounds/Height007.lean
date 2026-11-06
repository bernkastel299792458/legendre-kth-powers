import LegendreK6.M2Pilot.Enclosures.Height007
import LegendreK6.M2PilotIntegerData

/-! Join checked analytic enclosures to the exact dyadic witness table. -/
namespace LegendreK6.M2Pilot.FactorBounds.Height007
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem bounds (i : Fin 988) (hlo : 224 ≤ i.val) (hhi : i.val < 256) :
    heightFactor i ≤ heightDyadicFactor i ∧ heightPower i ≤ heightDyadicPower i := by
  interval_cases hi : i.val
  · have heq : i = (224 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height007.height_factor_upper_224.trans
      change ((53293886649175 / 8796093022208 : ℚ) : ℝ) ≤ ((1705404372773600 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height007.height_power_upper_224.trans
      change ((508781721968161 / 140737488355328 : ℚ) : ℝ) ≤ ((1017563443936322 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (225 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height007.height_factor_upper_225.trans
      change ((831721630817059 / 140737488355328 : ℚ) : ℝ) ≤ ((1663443261634118 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height007.height_power_upper_225.trans
      change ((1022097699004021 / 281474976710656 : ℚ) : ℝ) ≤ ((1022097699004021 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (226 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height007.height_factor_upper_226.trans
      change ((1622513708588243 / 281474976710656 : ℚ) : ℝ) ≤ ((1622513708588243 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height007.height_power_upper_226.trans
      change ((256657972047729 / 70368744177664 : ℚ) : ℝ) ≤ ((1026631888190916 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (227 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height007.height_factor_upper_227.trans
      change ((791295188405393 / 140737488355328 : ℚ) : ℝ) ≤ ((1582590376810786 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height007.height_power_upper_227.trans
      change ((515583005780353 / 140737488355328 : ℚ) : ℝ) ≤ ((1031166011560706 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (228 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height007.height_factor_upper_228.trans
      change ((1543648551212819 / 281474976710656 : ℚ) : ℝ) ≤ ((1543648551212819 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height007.height_power_upper_228.trans
      change ((1035700069176999 / 281474976710656 : ℚ) : ℝ) ≤ ((1035700069176999 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (229 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height007.height_factor_upper_229.trans
      change ((188208015399975 / 35184372088832 : ℚ) : ℝ) ≤ ((1505664123199800 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height007.height_power_upper_229.trans
      change ((260058515275827 / 70368744177664 : ℚ) : ℝ) ≤ ((1040234061103308 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (230 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height007.height_factor_upper_230.trans
      change ((734306787901489 / 140737488355328 : ℚ) : ℝ) ≤ ((1468613575802978 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height007.height_power_upper_230.trans
      change ((65297999212691 / 17592186044416 : ℚ) : ℝ) ≤ ((1044767987403056 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (231 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height007.height_factor_upper_231.trans
      change ((1432473969174941 / 281474976710656 : ℚ) : ℝ) ≤ ((1432473969174941 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height007.height_power_upper_231.trans
      change ((1049301848139575 / 281474976710656 : ℚ) : ℝ) ≤ ((1049301848139575 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (232 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height007.height_factor_upper_232.trans
      change ((349305731610099 / 70368744177664 : ℚ) : ℝ) ≤ ((1397222926440396 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height007.height_power_upper_232.trans
      change ((1053835643376103 / 281474976710656 : ℚ) : ℝ) ≤ ((1053835643376103 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (233 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height007.height_factor_upper_233.trans
      change ((681419309946751 / 140737488355328 : ℚ) : ℝ) ≤ ((1362838619893502 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height007.height_power_upper_233.trans
      change ((1058369373175787 / 281474976710656 : ℚ) : ℝ) ≤ ((1058369373175787 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (234 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height007.height_factor_upper_234.trans
      change ((166162469691657 / 35184372088832 : ℚ) : ℝ) ≤ ((1329299757533256 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height007.height_power_upper_234.trans
      change ((531451518800843 / 140737488355328 : ℚ) : ℝ) ≤ ((1062903037601686 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (235 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height007.height_factor_upper_235.trans
      change ((1296585569928683 / 281474976710656 : ℚ) : ℝ) ≤ ((1296585569928683 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height007.height_power_upper_235.trans
      change ((1067436636716763 / 281474976710656 : ℚ) : ℝ) ≤ ((1067436636716763 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (236 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height007.height_factor_upper_236.trans
      change ((1264675797405749 / 281474976710656 : ℚ) : ℝ) ≤ ((1264675797405749 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height007.height_power_upper_236.trans
      change ((535985085291947 / 140737488355328 : ℚ) : ℝ) ≤ ((1071970170583894 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (237 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height007.height_factor_upper_237.trans
      change ((1233550677548125 / 281474976710656 : ℚ) : ℝ) ≤ ((1233550677548125 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height007.height_power_upper_237.trans
      change ((538251819632931 / 140737488355328 : ℚ) : ℝ) ≤ ((1076503639265862 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (238 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height007.height_factor_upper_238.trans
      change ((300797733251031 / 70368744177664 : ℚ) : ℝ) ≤ ((1203190933004124 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height007.height_power_upper_238.trans
      change ((1081037042825359 / 281474976710656 : ℚ) : ℝ) ≤ ((1081037042825359 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (239 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height007.height_factor_upper_239.trans
      change ((1173577759592321 / 281474976710656 : ℚ) : ℝ) ≤ ((1173577759592321 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height007.height_power_upper_239.trans
      change ((542785190662495 / 140737488355328 : ℚ) : ℝ) ≤ ((1085570381324990 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (240 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height007.height_factor_upper_240.trans
      change ((1144692814698543 / 281474976710656 : ℚ) : ℝ) ≤ ((1144692814698543 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height007.height_power_upper_240.trans
      change ((545051827413633 / 140737488355328 : ℚ) : ℝ) ≤ ((1090103654827266 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (241 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height007.height_factor_upper_241.trans
      change ((279129551489277 / 70368744177664 : ℚ) : ℝ) ≤ ((1116518205957108 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height007.height_power_upper_241.trans
      change ((547318431697305 / 140737488355328 : ℚ) : ℝ) ≤ ((1094636863394610 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (242 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height007.height_factor_upper_242.trans
      change ((1089036480209337 / 281474976710656 : ℚ) : ℝ) ≤ ((1089036480209337 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height007.height_power_upper_242.trans
      change ((549585003544677 / 140737488355328 : ℚ) : ℝ) ≤ ((1099170007089354 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (243 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height007.height_factor_upper_243.trans
      change ((132778826591573 / 35184372088832 : ℚ) : ℝ) ≤ ((1062230612732584 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height007.height_power_upper_243.trans
      change ((1103703085973741 / 281474976710656 : ℚ) : ℝ) ≤ ((1103703085973741 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (244 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height007.height_factor_upper_244.trans
      change ((518041998366565 / 140737488355328 : ℚ) : ℝ) ≤ ((1036083996733130 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height007.height_power_upper_244.trans
      change ((1108236100109925 / 281474976710656 : ℚ) : ℝ) ≤ ((1108236100109925 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (245 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height007.height_factor_upper_245.trans
      change ((505290216548255 / 140737488355328 : ℚ) : ℝ) ≤ ((1010580433096510 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height007.height_power_upper_245.trans
      change ((1112769049559969 / 281474976710656 : ℚ) : ℝ) ≤ ((1112769049559969 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (246 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height007.height_factor_upper_246.trans
      change ((492852060194481 / 140737488355328 : ℚ) : ℝ) ≤ ((985704120388962 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height007.height_power_upper_246.trans
      change ((139662741798231 / 35184372088832 : ℚ) : ℝ) ≤ ((1117301934385848 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (247 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height007.height_factor_upper_247.trans
      change ((961439645103841 / 281474976710656 : ℚ) : ℝ) ≤ ((961439645103841 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height007.height_power_upper_247.trans
      change ((140229344331181 / 35184372088832 : ℚ) : ℝ) ≤ ((1121834754649448 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (248 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height007.height_factor_upper_248.trans
      change ((937771972147029 / 281474976710656 : ℚ) : ℝ) ≤ ((937771972147029 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height007.height_power_upper_248.trans
      change ((563183755206283 / 140737488355328 : ℚ) : ℝ) ≤ ((1126367510412566 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (249 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height007.height_factor_upper_249.trans
      change ((457343217777733 / 140737488355328 : ℚ) : ℝ) ≤ ((914686435555466 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height007.height_power_upper_249.trans
      change ((565450100868455 / 140737488355328 : ℚ) : ℝ) ≤ ((1130900201736910 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (250 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height007.height_factor_upper_250.trans
      change ((892168729443101 / 281474976710656 : ℚ) : ℝ) ≤ ((892168729443101 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height007.height_power_upper_250.trans
      change ((283858207171025 / 70368744177664 : ℚ) : ℝ) ≤ ((1135432828684100 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (251 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height007.height_factor_upper_251.trans
      change ((870204899168717 / 281474976710656 : ℚ) : ℝ) ≤ ((870204899168717 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height007.height_power_upper_251.trans
      change ((569982695657833 / 140737488355328 : ℚ) : ℝ) ≤ ((1139965391315666 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (252 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height007.height_factor_upper_252.trans
      change ((424390666360081 / 140737488355328 : ℚ) : ℝ) ≤ ((848781332720162 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height007.height_power_upper_252.trans
      change ((1144497889693053 / 281474976710656 : ℚ) : ℝ) ≤ ((1144497889693053 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (253 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height007.height_factor_upper_253.trans
      change ((25871398509679 / 8796093022208 : ℚ) : ℝ) ≤ ((827884752309728 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height007.height_power_upper_253.trans
      change ((1149030323877615 / 281474976710656 : ℚ) : ℝ) ≤ ((1149030323877615 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (254 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height007.height_factor_upper_254.trans
      change ((403751103087737 / 140737488355328 : ℚ) : ℝ) ≤ ((807502206175474 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height007.height_power_upper_254.trans
      change ((1153562693930619 / 281474976710656 : ℚ) : ℝ) ≤ ((1153562693930619 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (255 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height007.height_factor_upper_255.trans
      change ((787621060583481 / 281474976710656 : ℚ) : ℝ) ≤ ((787621060583481 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height007.height_power_upper_255.trans
      change ((579047499956623 / 140737488355328 : ℚ) : ℝ) ≤ ((1158094999913246 : ℕ) : ℝ) / 2^48
      norm_num
end LegendreK6.M2Pilot.FactorBounds.Height007
