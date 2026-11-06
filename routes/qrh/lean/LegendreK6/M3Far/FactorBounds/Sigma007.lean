import LegendreK6.M3Far.Enclosures.Sigma007
import LegendreK6.M3FarIntegerData

/-! Join checked analytic enclosures to the exact dyadic witness table. -/
namespace LegendreK6.M3Far.FactorBounds.Sigma007
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem bounds (i : Fin 384) (hlo : 224 ≤ i.val) (hhi : i.val < 256) :
    sigmaFactor i ≤ sigmaDyadicFactor i ∧ sigmaPower i ≤ sigmaDyadicPower i := by
  interval_cases hi : i.val
  · have heq : i = (224 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_224.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_224.trans
      change ((22884144448021 / 70368744177664 : ℚ) : ℝ) ≤ ((91536577792084 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (225 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_225.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_225.trans
      change ((91033859744713 / 281474976710656 : ℚ) : ℝ) ≤ ((91033859744713 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (226 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_226.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_226.trans
      change ((90530374188873 / 281474976710656 : ℚ) : ℝ) ≤ ((90530374188873 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (227 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_227.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_227.trans
      change ((1406658115087 / 4398046511104 : ℚ) : ℝ) ≤ ((90026119365568 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (228 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_228.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_228.trans
      change ((89521093510423 / 281474976710656 : ℚ) : ℝ) ≤ ((89521093510423 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (229 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_229.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_229.trans
      change ((2781727964177 / 8796093022208 : ℚ) : ℝ) ≤ ((89015294853664 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (230 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_230.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_230.trans
      change ((44254360810047 / 140737488355328 : ℚ) : ℝ) ≤ ((88508721620094 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (231 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_231.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_231.trans
      change ((88001372029079 / 281474976710656 : ℚ) : ℝ) ≤ ((88001372029079 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (232 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_232.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_232.trans
      change ((87493244294519 / 281474976710656 : ℚ) : ℝ) ≤ ((87493244294519 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (233 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_233.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_233.trans
      change ((43492168312417 / 140737488355328 : ℚ) : ℝ) ≤ ((86984336624834 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (234 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_234.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_234.trans
      change ((10809330902867 / 35184372088832 : ℚ) : ℝ) ≤ ((86474647222936 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (235 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_235.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_235.trans
      change ((85964174286217 / 281474976710656 : ℚ) : ℝ) ≤ ((85964174286217 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (236 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_236.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_236.trans
      change ((42726458003259 / 140737488355328 : ℚ) : ℝ) ≤ ((85452916006518 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (237 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_237.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_237.trans
      change ((42470435285057 / 140737488355328 : ℚ) : ℝ) ≤ ((84940870570114 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (238 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_238.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_238.trans
      change ((84428036157691 / 281474976710656 : ℚ) : ℝ) ≤ ((84428036157691 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (239 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_239.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_239.trans
      change ((20978602736081 / 70368744177664 : ℚ) : ℝ) ≤ ((83914410944324 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (240 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_240.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_240.trans
      change ((41699996549727 / 140737488355328 : ℚ) : ℝ) ≤ ((83399993099454 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (241 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_241.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_241.trans
      change ((82884780786871 / 281474976710656 : ℚ) : ℝ) ≤ ((82884780786871 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (242 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_242.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_242.trans
      change ((82368772164685 / 281474976710656 : ℚ) : ℝ) ≤ ((82368772164685 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (243 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_243.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_243.trans
      change ((81851965385311 / 281474976710656 : ℚ) : ℝ) ≤ ((81851965385311 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (244 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_244.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_244.trans
      change ((81334358595443 / 281474976710656 : ℚ) : ℝ) ≤ ((81334358595443 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (245 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_245.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_245.trans
      change ((2525498435501 / 8796093022208 : ℚ) : ℝ) ≤ ((80815949936032 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (246 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_246.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_246.trans
      change ((80296737542265 / 281474976710656 : ℚ) : ℝ) ≤ ((80296737542265 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (247 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_247.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_247.trans
      change ((79776719543543 / 281474976710656 : ℚ) : ℝ) ≤ ((79776719543543 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (248 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_248.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_248.trans
      change ((2476746689483 / 8796093022208 : ℚ) : ℝ) ≤ ((79255894063456 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (249 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_249.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_249.trans
      change ((19683564804941 / 70368744177664 : ℚ) : ℝ) ≤ ((78734259219764 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (250 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_250.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_250.trans
      change ((78211813124371 / 281474976710656 : ℚ) : ℝ) ≤ ((78211813124371 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (251 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_251.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_251.trans
      change ((77688553883305 / 281474976710656 : ℚ) : ℝ) ≤ ((77688553883305 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (252 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_252.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_252.trans
      change ((77164479596691 / 281474976710656 : ℚ) : ℝ) ≤ ((77164479596691 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (253 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_253.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_253.trans
      change ((76639588358735 / 281474976710656 : ℚ) : ℝ) ≤ ((76639588358735 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (254 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_254.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_254.trans
      change ((19028469564423 / 70368744177664 : ℚ) : ℝ) ≤ ((76113878257692 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (255 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_255.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_255.trans
      change ((18896836843963 / 70368744177664 : ℚ) : ℝ) ≤ ((75587347375852 : ℕ) : ℝ) / 2^48
      norm_num
end LegendreK6.M3Far.FactorBounds.Sigma007
