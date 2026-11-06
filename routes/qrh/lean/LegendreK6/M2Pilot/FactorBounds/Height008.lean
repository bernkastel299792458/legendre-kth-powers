import LegendreK6.M2Pilot.Enclosures.Height008
import LegendreK6.M2PilotIntegerData

/-! Join checked analytic enclosures to the exact dyadic witness table. -/
namespace LegendreK6.M2Pilot.FactorBounds.Height008
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem bounds (i : Fin 988) (hlo : 256 ≤ i.val) (hhi : i.val < 288) :
    heightFactor i ≤ heightDyadicFactor i ∧ heightPower i ≤ heightDyadicPower i := by
  interval_cases hi : i.val
  · have heq : i = (256 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height008.height_factor_upper_256.trans
      change ((768228992026101 / 281474976710656 : ℚ) : ℝ) ≤ ((768228992026101 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height008.height_power_upper_256.trans
      change ((1162627241886587 / 281474976710656 : ℚ) : ℝ) ≤ ((1162627241886587 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (257 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height008.height_factor_upper_257.trans
      change ((374656989805701 / 140737488355328 : ℚ) : ℝ) ≤ ((749313979611402 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height008.height_power_upper_257.trans
      change ((1167159419911647 / 281474976710656 : ℚ) : ℝ) ≤ ((1167159419911647 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (258 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height008.height_factor_upper_258.trans
      change ((730864297639147 / 281474976710656 : ℚ) : ℝ) ≤ ((730864297639147 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height008.height_power_upper_258.trans
      change ((18307680219521 / 4398046511104 : ℚ) : ℝ) ≤ ((1171691534049344 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (259 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height008.height_factor_upper_259.trans
      change ((712868508358711 / 281474976710656 : ℚ) : ℝ) ≤ ((712868508358711 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height008.height_power_upper_259.trans
      change ((1176223584360509 / 281474976710656 : ℚ) : ℝ) ≤ ((1176223584360509 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (260 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height008.height_factor_upper_260.trans
      change ((10864303982883 / 4398046511104 : ℚ) : ℝ) ≤ ((695315454904512 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height008.height_power_upper_260.trans
      change ((295188892726471 / 70368744177664 : ℚ) : ℝ) ≤ ((1180755570905884 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (261 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height008.height_factor_upper_261.trans
      change ((678194254404583 / 281474976710656 : ℚ) : ℝ) ≤ ((678194254404583 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height008.height_power_upper_261.trans
      change ((74080468359133 / 17592186044416 : ℚ) : ℝ) ≤ ((1185287493746128 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (262 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height008.height_factor_upper_262.trans
      change ((330747145629031 / 140737488355328 : ℚ) : ℝ) ≤ ((661494291258062 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height008.height_power_upper_262.trans
      change ((1189819352941811 / 281474976710656 : ℚ) : ℝ) ≤ ((1189819352941811 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (263 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height008.height_factor_upper_263.trans
      change ((80650651322183 / 35184372088832 : ℚ) : ℝ) ≤ ((645205210577464 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height008.height_power_upper_263.trans
      change ((1194351148553417 / 281474976710656 : ℚ) : ℝ) ≤ ((1194351148553417 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (264 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height008.height_factor_upper_264.trans
      change ((314658455895843 / 140737488355328 : ℚ) : ℝ) ≤ ((629316911791686 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height008.height_power_upper_264.trans
      change ((1198882880641345 / 281474976710656 : ℚ) : ℝ) ≤ ((1198882880641345 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (265 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height008.height_factor_upper_265.trans
      change ((613819542405827 / 281474976710656 : ℚ) : ℝ) ≤ ((613819542405827 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height008.height_power_upper_265.trans
      change ((601707274632953 / 140737488355328 : ℚ) : ℝ) ≤ ((1203414549265906 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (266 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height008.height_factor_upper_266.trans
      change ((37418968244623 / 17592186044416 : ℚ) : ℝ) ≤ ((598703491913968 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height008.height_power_upper_266.trans
      change ((603973077243663 / 140737488355328 : ℚ) : ℝ) ≤ ((1207946154487326 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (267 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height008.height_factor_upper_267.trans
      change ((291979692930591 / 140737488355328 : ℚ) : ℝ) ≤ ((583959385861182 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height008.height_power_upper_267.trans
      change ((1212477696365747 / 281474976710656 : ℚ) : ℝ) ≤ ((1212477696365747 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (268 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height008.height_factor_upper_268.trans
      change ((569578080051099 / 281474976710656 : ℚ) : ℝ) ≤ ((569578080051099 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height008.height_power_upper_268.trans
      change ((608504587480611 / 140737488355328 : ℚ) : ℝ) ≤ ((1217009174961222 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (269 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height008.height_factor_upper_269.trans
      change ((69443831861935 / 35184372088832 : ℚ) : ℝ) ≤ ((555550654895480 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height008.height_power_upper_269.trans
      change ((610770295166861 / 140737488355328 : ℚ) : ℝ) ≤ ((1221540590333722 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (270 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height008.height_factor_upper_270.trans
      change ((135467102475579 / 70368744177664 : ℚ) : ℝ) ≤ ((541868409902316 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height008.height_power_upper_270.trans
      change ((306517985635783 / 70368744177664 : ℚ) : ℝ) ≤ ((1226071942543132 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (271 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height008.height_factor_upper_271.trans
      change ((264261429149527 / 140737488355328 : ℚ) : ℝ) ≤ ((528522858299054 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height008.height_power_upper_271.trans
      change ((1230603231649249 / 281474976710656 : ℚ) : ℝ) ≤ ((1230603231649249 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (272 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height008.height_factor_upper_272.trans
      change ((257752860893823 / 140737488355328 : ℚ) : ℝ) ≤ ((515505721787646 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height008.height_power_upper_272.trans
      change ((617567228855895 / 140737488355328 : ℚ) : ℝ) ≤ ((1235134457711790 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (273 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height008.height_factor_upper_273.trans
      change ((502808925428195 / 281474976710656 : ℚ) : ℝ) ≤ ((502808925428195 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height008.height_power_upper_273.trans
      change ((77479101299399 / 17592186044416 : ℚ) : ℝ) ≤ ((1239665620790384 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (274 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height008.height_factor_upper_274.trans
      change ((490424592648041 / 281474976710656 : ℚ) : ℝ) ≤ ((490424592648041 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height008.height_power_upper_274.trans
      change ((19440573764759 / 4398046511104 : ℚ) : ℝ) ≤ ((1244196720944576 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (275 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height008.height_factor_upper_275.trans
      change ((478345040373217 / 281474976710656 : ℚ) : ℝ) ≤ ((478345040373217 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height008.height_power_upper_275.trans
      change ((624363879116913 / 140737488355328 : ℚ) : ℝ) ≤ ((1248727758233826 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (276 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height008.height_factor_upper_276.trans
      change ((116640693569821 / 70368744177664 : ℚ) : ℝ) ≤ ((466562774279284 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height008.height_power_upper_276.trans
      change ((156657341589689 / 35184372088832 : ℚ) : ℝ) ≤ ((1253258732717512 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (277 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height008.height_factor_upper_277.trans
      change ((113767621039653 / 70368744177664 : ℚ) : ℝ) ≤ ((455070484158612 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height008.height_power_upper_277.trans
      change ((628894822227463 / 140737488355328 : ℚ) : ℝ) ≤ ((1257789644454926 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (278 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height008.height_factor_upper_278.trans
      change ((443861039401257 / 281474976710656 : ℚ) : ℝ) ≤ ((443861039401257 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height008.height_power_upper_278.trans
      change ((315580123376319 / 70368744177664 : ℚ) : ℝ) ≤ ((1262320493505276 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (279 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height008.height_factor_upper_279.trans
      change ((432927484586657 / 281474976710656 : ℚ) : ℝ) ≤ ((432927484586657 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height008.height_power_upper_279.trans
      change ((1266851279927687 / 281474976710656 : ℚ) : ℝ) ≤ ((1266851279927687 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (280 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height008.height_factor_upper_280.trans
      change ((211131517591713 / 140737488355328 : ℚ) : ℝ) ≤ ((422263035183426 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height008.height_power_upper_280.trans
      change ((1271382003781201 / 281474976710656 : ℚ) : ℝ) ≤ ((1271382003781201 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (281 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height008.height_factor_upper_281.trans
      change ((102965268338649 / 70368744177664 : ℚ) : ℝ) ≤ ((411861073354596 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height008.height_power_upper_281.trans
      change ((1275912665124775 / 281474976710656 : ℚ) : ℝ) ≤ ((1275912665124775 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (282 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height008.height_factor_upper_282.trans
      change ((200857571932867 / 140737488355328 : ℚ) : ℝ) ≤ ((401715143865734 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height008.height_power_upper_282.trans
      change ((1280443264017283 / 281474976710656 : ℚ) : ℝ) ≤ ((1280443264017283 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (283 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height008.height_factor_upper_283.trans
      change ((391818950093403 / 281474976710656 : ℚ) : ℝ) ≤ ((391818950093403 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height008.height_power_upper_283.trans
      change ((642486900258759 / 140737488355328 : ℚ) : ℝ) ≤ ((1284973800517518 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (284 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height008.height_factor_upper_284.trans
      change ((382166350131517 / 281474976710656 : ℚ) : ℝ) ≤ ((382166350131517 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height008.height_power_upper_284.trans
      change ((644752137342093 / 140737488355328 : ℚ) : ℝ) ≤ ((1289504274684186 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (285 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height008.height_factor_upper_285.trans
      change ((186375676496589 / 140737488355328 : ℚ) : ℝ) ≤ ((372751352993178 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height008.height_power_upper_285.trans
      change ((1294034686575915 / 281474976710656 : ℚ) : ℝ) ≤ ((1294034686575915 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (286 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height008.height_factor_upper_286.trans
      change ((181784057452841 / 140737488355328 : ℚ) : ℝ) ≤ ((363568114905682 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height008.height_power_upper_286.trans
      change ((649282518125623 / 140737488355328 : ℚ) : ℝ) ≤ ((1298565036251246 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (287 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height008.height_factor_upper_287.trans
      change ((354610935696373 / 281474976710656 : ℚ) : ℝ) ≤ ((354610935696373 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height008.height_power_upper_287.trans
      change ((1303095323768639 / 281474976710656 : ℚ) : ℝ) ≤ ((1303095323768639 : ℕ) : ℝ) / 2^48
      norm_num
end LegendreK6.M2Pilot.FactorBounds.Height008
