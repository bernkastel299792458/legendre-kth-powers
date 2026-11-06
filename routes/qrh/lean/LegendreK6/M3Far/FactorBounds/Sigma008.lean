import LegendreK6.M3Far.Enclosures.Sigma008
import LegendreK6.M3FarIntegerData

/-! Join checked analytic enclosures to the exact dyadic witness table. -/
namespace LegendreK6.M3Far.FactorBounds.Sigma008
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem bounds (i : Fin 384) (hlo : 256 ≤ i.val) (hhi : i.val < 288) :
    sigmaFactor i ≤ sigmaDyadicFactor i ∧ sigmaPower i ≤ sigmaDyadicPower i := by
  interval_cases hi : i.val
  · have heq : i = (256 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_256.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_256.trans
      change ((75059993789509 / 281474976710656 : ℚ) : ℝ) ≤ ((75059993789509 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (257 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_257.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_257.trans
      change ((74531815568941 / 281474976710656 : ℚ) : ℝ) ≤ ((74531815568941 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (258 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_258.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_258.trans
      change ((74002810778389 / 281474976710656 : ℚ) : ℝ) ≤ ((74002810778389 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (259 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_259.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_259.trans
      change ((73472977476027 / 281474976710656 : ℚ) : ℝ) ≤ ((73472977476027 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (260 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_260.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_260.trans
      change ((72942313713943 / 281474976710656 : ℚ) : ℝ) ≤ ((72942313713943 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (261 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_261.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_261.trans
      change ((36205408769057 / 140737488355328 : ℚ) : ℝ) ≤ ((72410817538114 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (262 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_262.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_262.trans
      change ((2246202718387 / 8796093022208 : ℚ) : ℝ) ≤ ((71878486988384 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (263 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_263.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_263.trans
      change ((71345320098433 / 281474976710656 : ℚ) : ℝ) ≤ ((71345320098433 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (264 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_264.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_264.trans
      change ((70811314895763 / 281474976710656 : ℚ) : ℝ) ≤ ((70811314895763 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (265 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_265.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_265.trans
      change ((1098069834401 / 4398046511104 : ℚ) : ℝ) ≤ ((70276469401664 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (266 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_266.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_266.trans
      change ((69740781631197 / 281474976710656 : ℚ) : ℝ) ≤ ((69740781631197 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (267 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_267.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_267.trans
      change ((17301062398291 / 70368744177664 : ℚ) : ℝ) ≤ ((69204249593164 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (268 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_268.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_268.trans
      change ((68666871290087 / 281474976710656 : ℚ) : ℝ) ≤ ((68666871290087 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (269 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_269.trans
      change ((1 / 140737488355328 : ℚ) : ℝ) ≤ ((2 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_269.trans
      change ((68128644718181 / 281474976710656 : ℚ) : ℝ) ≤ ((68128644718181 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (270 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_270.trans
      change ((1 / 140737488355328 : ℚ) : ℝ) ≤ ((2 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_270.trans
      change ((33794783933665 / 140737488355328 : ℚ) : ℝ) ≤ ((67589567867330 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (271 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_271.trans
      change ((1 / 140737488355328 : ℚ) : ℝ) ≤ ((2 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_271.trans
      change ((67049638721063 / 281474976710656 : ℚ) : ℝ) ≤ ((67049638721063 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (272 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_272.trans
      change ((3 / 281474976710656 : ℚ) : ℝ) ≤ ((3 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_272.trans
      change ((66508855256527 / 281474976710656 : ℚ) : ℝ) ≤ ((66508855256527 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (273 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_273.trans
      change ((3 / 281474976710656 : ℚ) : ℝ) ≤ ((3 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_273.trans
      change ((65967215444461 / 281474976710656 : ℚ) : ℝ) ≤ ((65967215444461 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (274 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_274.trans
      change ((1 / 70368744177664 : ℚ) : ℝ) ≤ ((4 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_274.trans
      change ((8178089656147 / 35184372088832 : ℚ) : ℝ) ≤ ((65424717249176 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (275 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_275.trans
      change ((1 / 70368744177664 : ℚ) : ℝ) ≤ ((4 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_275.trans
      change ((64881358628521 / 281474976710656 : ℚ) : ℝ) ≤ ((64881358628521 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (276 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_276.trans
      change ((5 / 281474976710656 : ℚ) : ℝ) ≤ ((5 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_276.trans
      change ((64337137533865 / 281474976710656 : ℚ) : ℝ) ≤ ((64337137533865 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (277 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_277.trans
      change ((3 / 140737488355328 : ℚ) : ℝ) ≤ ((6 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_277.trans
      change ((63792051910067 / 281474976710656 : ℚ) : ℝ) ≤ ((63792051910067 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (278 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_278.trans
      change ((7 / 281474976710656 : ℚ) : ℝ) ≤ ((7 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_278.trans
      change ((63246099695453 / 281474976710656 : ℚ) : ℝ) ≤ ((63246099695453 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (279 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_279.trans
      change ((9 / 281474976710656 : ℚ) : ℝ) ≤ ((9 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_279.trans
      change ((62699278821785 / 281474976710656 : ℚ) : ℝ) ≤ ((62699278821785 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (280 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_280.trans
      change ((5 / 140737488355328 : ℚ) : ℝ) ≤ ((10 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_280.trans
      change ((62151587214243 / 281474976710656 : ℚ) : ℝ) ≤ ((62151587214243 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (281 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_281.trans
      change ((3 / 70368744177664 : ℚ) : ℝ) ≤ ((12 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_281.trans
      change ((30801511395695 / 140737488355328 : ℚ) : ℝ) ≤ ((61603022791390 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (282 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_282.trans
      change ((15 / 281474976710656 : ℚ) : ℝ) ≤ ((15 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_282.trans
      change ((61053583465151 / 281474976710656 : ℚ) : ℝ) ≤ ((61053583465151 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (283 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_283.trans
      change ((17 / 281474976710656 : ℚ) : ℝ) ≤ ((17 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_283.trans
      change ((60503267140785 / 281474976710656 : ℚ) : ℝ) ≤ ((60503267140785 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (284 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_284.trans
      change ((21 / 281474976710656 : ℚ) : ℝ) ≤ ((21 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_284.trans
      change ((14988017929215 / 70368744177664 : ℚ) : ℝ) ≤ ((59952071716860 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (285 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_285.trans
      change ((25 / 281474976710656 : ℚ) : ℝ) ≤ ((25 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_285.trans
      change ((59399995085223 / 281474976710656 : ℚ) : ℝ) ≤ ((59399995085223 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (286 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_286.trans
      change ((15 / 140737488355328 : ℚ) : ℝ) ≤ ((30 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_286.trans
      change ((58847035130975 / 281474976710656 : ℚ) : ℝ) ≤ ((58847035130975 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (287 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma008.sigma_factor_upper_287.trans
      change ((9 / 70368744177664 : ℚ) : ℝ) ≤ ((36 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma008.sigma_power_upper_287.trans
      change ((58293189732445 / 281474976710656 : ℚ) : ℝ) ≤ ((58293189732445 : ℕ) : ℝ) / 2^48
      norm_num
end LegendreK6.M3Far.FactorBounds.Sigma008
