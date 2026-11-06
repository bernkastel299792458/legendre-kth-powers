import LegendreK6.M2Pilot.Enclosures.Sigma002
import LegendreK6.M2PilotIntegerData

/-! Join checked analytic enclosures to the exact dyadic witness table. -/
namespace LegendreK6.M2Pilot.FactorBounds.Sigma002
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem bounds (i : Fin 1536) (hlo : 256 ≤ i.val) (hhi : i.val < 384) :
    sigmaFactor i ≤ sigmaDyadicFactor i ∧ sigmaPower i ≤ sigmaDyadicPower i := by
  interval_cases hi : i.val
  · have heq : i = (256 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_256.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_256.trans
      change ((81586949771205 / 140737488355328 : ℚ) : ℝ) ≤ ((163173899542410 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (257 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_257.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_257.trans
      change ((40768528986233 / 70368744177664 : ℚ) : ℝ) ≤ ((163074115944932 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (258 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_258.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_258.trans
      change ((40743574610513 / 70368744177664 : ℚ) : ℝ) ≤ ((162974298442052 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (259 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_259.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_259.trans
      change ((162874447016487 / 281474976710656 : ℚ) : ℝ) ≤ ((162874447016487 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (260 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_260.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_260.trans
      change ((40693640412735 / 70368744177664 : ℚ) : ℝ) ≤ ((162774561650940 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (261 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_261.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_261.trans
      change ((20334330291013 / 35184372088832 : ℚ) : ℝ) ≤ ((162674642328104 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (262 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_262.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_262.trans
      change ((162574689030659 / 281474976710656 : ℚ) : ℝ) ≤ ((162574689030659 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (263 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_263.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_263.trans
      change ((40618675435319 / 70368744177664 : ℚ) : ℝ) ≤ ((162474701741276 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (264 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_264.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_264.trans
      change ((81187340221305 / 140737488355328 : ℚ) : ℝ) ≤ ((162374680442610 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (265 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_265.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_265.trans
      change ((40568656279327 / 70368744177664 : ℚ) : ℝ) ≤ ((162274625117308 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (266 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_266.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_266.trans
      change ((81087267874001 / 140737488355328 : ℚ) : ℝ) ≤ ((162174535748002 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (267 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_267.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_267.trans
      change ((162074412317315 / 281474976710656 : ℚ) : ℝ) ≤ ((162074412317315 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (268 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_268.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_268.trans
      change ((161974254807857 / 281474976710656 : ℚ) : ℝ) ≤ ((161974254807857 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (269 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_269.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_269.trans
      change ((161874063202225 / 281474976710656 : ℚ) : ℝ) ≤ ((161874063202225 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (270 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_270.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_270.trans
      change ((80886918741503 / 140737488355328 : ℚ) : ℝ) ≤ ((161773837483006 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (271 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_271.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_271.trans
      change ((80836788816387 / 140737488355328 : ℚ) : ℝ) ≤ ((161673577632774 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (272 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_272.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_272.trans
      change ((40393320908523 / 70368744177664 : ℚ) : ℝ) ≤ ((161573283634092 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (273 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_273.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_273.trans
      change ((80736477734755 / 140737488355328 : ℚ) : ℝ) ≤ ((161472955469510 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (274 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_274.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_274.trans
      change ((161372593121567 / 281474976710656 : ℚ) : ℝ) ≤ ((161372593121567 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (275 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_275.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_275.trans
      change ((80636098286395 / 140737488355328 : ℚ) : ℝ) ≤ ((161272196572790 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (276 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_276.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_276.trans
      change ((161171765805693 / 281474976710656 : ℚ) : ℝ) ≤ ((161171765805693 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (277 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_277.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_277.trans
      change ((40267825200695 / 70368744177664 : ℚ) : ℝ) ≤ ((161071300802780 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (278 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_278.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_278.trans
      change ((80485400773271 / 140737488355328 : ℚ) : ℝ) ≤ ((160970801546542 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (279 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_279.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_279.trans
      change ((80435134009729 / 140737488355328 : ℚ) : ℝ) ≤ ((160870268019458 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (280 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_280.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_280.trans
      change ((160769700203995 / 281474976710656 : ℚ) : ℝ) ≤ ((160769700203995 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (281 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_281.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_281.trans
      change ((10041818630163 / 17592186044416 : ℚ) : ℝ) ≤ ((160669098082608 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (282 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_282.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_282.trans
      change ((160568461637741 / 281474976710656 : ℚ) : ℝ) ≤ ((160568461637741 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (283 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_283.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_283.trans
      change ((10029236928239 / 17592186044416 : ℚ) : ℝ) ≤ ((160467790851824 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (284 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_284.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_284.trans
      change ((80183542853639 / 140737488355328 : ℚ) : ℝ) ≤ ((160367085707278 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (285 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_285.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_285.trans
      change ((40066586546627 / 70368744177664 : ℚ) : ℝ) ≤ ((160266346186508 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (286 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_286.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_286.trans
      change ((160165572271911 / 281474976710656 : ℚ) : ℝ) ≤ ((160165572271911 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (287 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_287.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_287.trans
      change ((80032381972935 / 140737488355328 : ℚ) : ℝ) ≤ ((160064763945870 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (288 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_288.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_288.trans
      change ((39990980297689 / 70368744177664 : ℚ) : ℝ) ≤ ((159963921190756 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (289 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_289.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_289.trans
      change ((2497860062327 / 4398046511104 : ℚ) : ℝ) ≤ ((159863043988928 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (290 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_290.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_290.trans
      change ((39940533080683 / 70368744177664 : ℚ) : ℝ) ≤ ((159762132322732 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (291 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_291.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_291.trans
      change ((79830593087253 / 140737488355328 : ℚ) : ℝ) ≤ ((159661186174506 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (292 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_292.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_292.trans
      change ((79780102763285 / 140737488355328 : ℚ) : ℝ) ≤ ((159560205526570 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (293 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_293.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_293.trans
      change ((39864797590309 / 70368744177664 : ℚ) : ℝ) ≤ ((159459190361236 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (294 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_294.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_294.trans
      change ((159358140660803 / 281474976710656 : ℚ) : ℝ) ≤ ((159358140660803 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (295 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_295.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_295.trans
      change ((159257056407557 / 281474976710656 : ℚ) : ℝ) ≤ ((159257056407557 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (296 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_296.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_296.trans
      change ((159155937583773 / 281474976710656 : ℚ) : ℝ) ≤ ((159155937583773 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (297 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_297.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_297.trans
      change ((79527392085857 / 140737488355328 : ℚ) : ℝ) ≤ ((159054784171714 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (298 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_298.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_298.trans
      change ((158953596153629 / 281474976710656 : ℚ) : ℝ) ≤ ((158953596153629 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (299 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_299.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_299.trans
      change ((158852373511757 / 281474976710656 : ℚ) : ℝ) ≤ ((158852373511757 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (300 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_300.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_300.trans
      change ((39687779057081 / 70368744177664 : ℚ) : ℝ) ≤ ((158751116228324 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (301 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_301.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_301.trans
      change ((158649824285543 / 281474976710656 : ℚ) : ℝ) ≤ ((158649824285543 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (302 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_302.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_302.trans
      change ((158548497665617 / 281474976710656 : ℚ) : ℝ) ≤ ((158548497665617 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (303 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_303.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_303.trans
      change ((79223568175367 / 140737488355328 : ℚ) : ℝ) ≤ ((158447136350734 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (304 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_304.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_304.trans
      change ((158345740323073 / 281474976710656 : ℚ) : ℝ) ≤ ((158345740323073 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (305 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_305.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_305.trans
      change ((158244309564797 / 281474976710656 : ℚ) : ℝ) ≤ ((158244309564797 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (306 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_306.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_306.trans
      change ((39535711014515 / 70368744177664 : ℚ) : ℝ) ≤ ((158142844058060 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (307 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_307.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_307.trans
      change ((79020671892501 / 140737488355328 : ℚ) : ℝ) ≤ ((158041343785002 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (308 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_308.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_308.trans
      change ((157939808727753 / 281474976710656 : ℚ) : ℝ) ≤ ((157939808727753 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (309 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_309.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_309.trans
      change ((157838238868427 / 281474976710656 : ℚ) : ℝ) ≤ ((157838238868427 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (310 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_310.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_310.trans
      change ((19717079273641 / 35184372088832 : ℚ) : ℝ) ≤ ((157736634189128 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (311 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_311.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_311.trans
      change ((157634994671949 / 281474976710656 : ℚ) : ℝ) ≤ ((157634994671949 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (312 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_312.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_312.trans
      change ((19691665037371 / 35184372088832 : ℚ) : ℝ) ≤ ((157533320298968 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (313 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_313.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_313.trans
      change ((157431611052253 / 281474976710656 : ℚ) : ℝ) ≤ ((157431611052253 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (314 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_314.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_314.trans
      change ((78664933456929 / 140737488355328 : ℚ) : ℝ) ≤ ((157329866913858 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (315 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_315.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_315.trans
      change ((78614043932913 / 140737488355328 : ℚ) : ℝ) ≤ ((157228087865826 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (316 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_316.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_316.trans
      change ((78563136945093 / 140737488355328 : ℚ) : ℝ) ≤ ((157126273890186 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (317 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_317.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_317.trans
      change ((39256106242239 / 70368744177664 : ℚ) : ℝ) ≤ ((157024424968956 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (318 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_318.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_318.trans
      change ((78461270542071 / 140737488355328 : ℚ) : ℝ) ≤ ((156922541084142 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (319 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_319.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_319.trans
      change ((156820622217737 / 281474976710656 : ℚ) : ℝ) ≤ ((156820622217737 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (320 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_320.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_320.trans
      change ((156718668351721 / 281474976710656 : ℚ) : ℝ) ≤ ((156718668351721 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (321 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_321.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_321.trans
      change ((156616679468063 / 281474976710656 : ℚ) : ℝ) ≤ ((156616679468063 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (322 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_322.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_322.trans
      change ((156514655548717 / 281474976710656 : ℚ) : ℝ) ≤ ((156514655548717 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (323 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_323.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_323.trans
      change ((156412596575629 / 281474976710656 : ℚ) : ℝ) ≤ ((156412596575629 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (324 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_324.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_324.trans
      change ((156310502530729 / 281474976710656 : ℚ) : ℝ) ≤ ((156310502530729 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (325 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_325.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_325.trans
      change ((156208373395935 / 281474976710656 : ℚ) : ℝ) ≤ ((156208373395935 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (326 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_326.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_326.trans
      change ((156106209153155 / 281474976710656 : ℚ) : ℝ) ≤ ((156106209153155 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (327 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_327.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_327.trans
      change ((19500501223035 / 35184372088832 : ℚ) : ℝ) ≤ ((156004009784280 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (328 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_328.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_328.trans
      change ((77950887635597 / 140737488355328 : ℚ) : ℝ) ≤ ((155901775271194 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (329 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_329.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_329.trans
      change ((38949876398941 / 70368744177664 : ℚ) : ℝ) ≤ ((155799505595764 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (330 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_330.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_330.trans
      change ((155697200739847 / 281474976710656 : ℚ) : ℝ) ≤ ((155697200739847 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (331 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_331.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_331.trans
      change ((19449357585661 / 35184372088832 : ℚ) : ℝ) ≤ ((155594860685288 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (332 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_332.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_332.trans
      change ((38873121353479 / 70368744177664 : ℚ) : ℝ) ≤ ((155492485413916 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (333 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_333.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_333.trans
      change ((4855939840861 / 8796093022208 : ℚ) : ℝ) ≤ ((155390074907552 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (334 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_334.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_334.trans
      change ((77643814574001 / 140737488355328 : ℚ) : ℝ) ≤ ((155287629148002 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (335 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_335.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_335.trans
      change ((155185148117059 / 281474976710656 : ℚ) : ℝ) ≤ ((155185148117059 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (336 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_336.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_336.trans
      change ((155082631796505 / 281474976710656 : ℚ) : ℝ) ≤ ((155082631796505 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (337 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_337.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_337.trans
      change ((154980080168109 / 281474976710656 : ℚ) : ℝ) ≤ ((154980080168109 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (338 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_338.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_338.trans
      change ((77438746606813 / 140737488355328 : ℚ) : ℝ) ≤ ((154877493213626 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (339 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_339.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_339.trans
      change ((9673429432175 / 17592186044416 : ℚ) : ℝ) ≤ ((154774870914800 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (340 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_340.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_340.trans
      change ((38668053313341 / 70368744177664 : ℚ) : ℝ) ≤ ((154672213253364 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (341 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_341.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_341.trans
      change ((154569520211033 / 281474976710656 : ℚ) : ℝ) ≤ ((154569520211033 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (342 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_342.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_342.trans
      change ((38616697942379 / 70368744177664 : ℚ) : ℝ) ≤ ((154466791769516 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (343 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_343.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_343.trans
      change ((19295503488813 / 35184372088832 : ℚ) : ℝ) ≤ ((154364027910504 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (344 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_344.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_344.trans
      change ((75322865535 / 137438953472 : ℚ) : ℝ) ≤ ((154261228615680 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (345 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_345.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_345.trans
      change ((154158393866709 / 281474976710656 : ℚ) : ℝ) ≤ ((154158393866709 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (346 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_346.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_346.trans
      change ((154055523645249 / 281474976710656 : ℚ) : ℝ) ≤ ((154055523645249 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (347 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_347.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_347.trans
      change ((153952617932941 / 281474976710656 : ℚ) : ℝ) ≤ ((153952617932941 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (348 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_348.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_348.trans
      change ((153849676711415 / 281474976710656 : ℚ) : ℝ) ≤ ((153849676711415 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (349 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_349.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_349.trans
      change ((153746699962289 / 281474976710656 : ℚ) : ℝ) ≤ ((153746699962289 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (350 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_350.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_350.trans
      change ((4801365239599 / 8796093022208 : ℚ) : ℝ) ≤ ((153643687667168 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (351 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_351.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_351.trans
      change ((153540639807643 / 281474976710656 : ℚ) : ℝ) ≤ ((153540639807643 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (352 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_352.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_352.trans
      change ((76718778182647 / 140737488355328 : ℚ) : ℝ) ≤ ((153437556365294 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (353 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_353.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_353.trans
      change ((76667218660843 / 140737488355328 : ℚ) : ℝ) ≤ ((153334437321686 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (354 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_354.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_354.trans
      change ((153231282658375 / 281474976710656 : ℚ) : ℝ) ≤ ((153231282658375 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (355 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_355.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_355.trans
      change ((38282023089225 / 70368744177664 : ℚ) : ℝ) ≤ ((153128092356900 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (356 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_356.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_356.trans
      change ((153024866398791 / 281474976710656 : ℚ) : ℝ) ≤ ((153024866398791 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (357 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_357.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_357.trans
      change ((76460802382781 / 140737488355328 : ℚ) : ℝ) ≤ ((152921604765562 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (358 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_358.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_358.trans
      change ((38204576859679 / 70368744177664 : ℚ) : ℝ) ≤ ((152818307438716 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (359 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_359.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_359.trans
      change ((152714974399743 / 281474976710656 : ℚ) : ℝ) ≤ ((152714974399743 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (360 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_360.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_360.trans
      change ((152611605630121 / 281474976710656 : ℚ) : ℝ) ≤ ((152611605630121 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (361 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_361.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_361.trans
      change ((152508201111313 / 281474976710656 : ℚ) : ℝ) ≤ ((152508201111313 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (362 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_362.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_362.trans
      change ((38101190206193 / 70368744177664 : ℚ) : ℝ) ≤ ((152404760824772 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (363 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_363.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_363.trans
      change ((152301284751935 / 281474976710656 : ℚ) : ℝ) ≤ ((152301284751935 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (364 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_364.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_364.trans
      change ((38049443218557 / 70368744177664 : ℚ) : ℝ) ≤ ((152197772874228 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (365 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_365.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_365.trans
      change ((152094225173065 / 281474976710656 : ℚ) : ℝ) ≤ ((152094225173065 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (366 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_366.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_366.trans
      change ((75995320814923 / 140737488355328 : ℚ) : ℝ) ≤ ((151990641629846 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (367 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_367.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_367.trans
      change ((151887022225957 / 281474976710656 : ℚ) : ℝ) ≤ ((151887022225957 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (368 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_368.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_368.trans
      change ((151783366942773 / 281474976710656 : ℚ) : ℝ) ≤ ((151783366942773 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (369 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_369.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_369.trans
      change ((18959959470207 / 35184372088832 : ℚ) : ℝ) ≤ ((151679675761656 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (370 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_370.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_370.trans
      change ((75787974331977 / 140737488355328 : ℚ) : ℝ) ≤ ((151575948663954 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (371 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_371.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_371.trans
      change ((75736092815501 / 140737488355328 : ℚ) : ℝ) ≤ ((151472185631002 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (372 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_372.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_372.trans
      change ((151368386644123 / 281474976710656 : ℚ) : ℝ) ≤ ((151368386644123 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (373 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_373.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_373.trans
      change ((151264551684627 / 281474976710656 : ℚ) : ℝ) ≤ ((151264551684627 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (374 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_374.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_374.trans
      change ((151160680733811 / 281474976710656 : ℚ) : ℝ) ≤ ((151160680733811 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (375 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_375.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_375.trans
      change ((75528386886479 / 140737488355328 : ℚ) : ℝ) ≤ ((151056773772958 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (376 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_376.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_376.trans
      change ((150952830783339 / 281474976710656 : ℚ) : ℝ) ≤ ((150952830783339 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (377 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_377.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_377.trans
      change ((37712212936553 / 70368744177664 : ℚ) : ℝ) ≤ ((150848851746212 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (378 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_378.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_378.trans
      change ((150744836642821 / 281474976710656 : ℚ) : ℝ) ≤ ((150744836642821 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (379 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_379.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_379.trans
      change ((2353762272725 / 4398046511104 : ℚ) : ℝ) ≤ ((150640785454400 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (380 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_380.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_380.trans
      change ((150536698162165 / 281474976710656 : ℚ) : ℝ) ≤ ((150536698162165 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (381 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_381.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_381.trans
      change ((150432574747323 / 281474976710656 : ℚ) : ℝ) ≤ ((150432574747323 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (382 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_382.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_382.trans
      change ((150328415191067 / 281474976710656 : ℚ) : ℝ) ≤ ((150328415191067 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (383 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_383.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_383.trans
      change ((9389013717161 / 17592186044416 : ℚ) : ℝ) ≤ ((150224219474576 : ℕ) : ℝ) / 2^48
      norm_num
end LegendreK6.M2Pilot.FactorBounds.Sigma002
