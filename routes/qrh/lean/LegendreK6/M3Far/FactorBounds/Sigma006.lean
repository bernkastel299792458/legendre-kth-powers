import LegendreK6.M3Far.Enclosures.Sigma006
import LegendreK6.M3FarIntegerData

/-! Join checked analytic enclosures to the exact dyadic witness table. -/
namespace LegendreK6.M3Far.FactorBounds.Sigma006
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem bounds (i : Fin 384) (hlo : 192 ≤ i.val) (hhi : i.val < 224) :
    sigmaFactor i ≤ sigmaDyadicFactor i ∧ sigmaPower i ≤ sigmaDyadicPower i := by
  interval_cases hi : i.val
  · have heq : i = (192 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_192.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_192.trans
      change ((107228562556441 / 281474976710656 : ℚ) : ℝ) ≤ ((107228562556441 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (193 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_193.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_193.trans
      change ((53374753588221 / 140737488355328 : ℚ) : ℝ) ≤ ((106749507176442 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (194 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_194.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_194.trans
      change ((106269737853999 / 281474976710656 : ℚ) : ℝ) ≤ ((106269737853999 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (195 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_195.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_195.trans
      change ((105789252991925 / 281474976710656 : ℚ) : ℝ) ≤ ((105789252991925 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (196 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_196.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_196.trans
      change ((52654025494133 / 140737488355328 : ℚ) : ℝ) ≤ ((105308050988266 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (197 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_197.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_197.trans
      change ((52413065118141 / 140737488355328 : ℚ) : ℝ) ≤ ((104826130236282 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (198 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_198.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_198.trans
      change ((104343489124429 / 281474976710656 : ℚ) : ℝ) ≤ ((104343489124429 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (199 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_199.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_199.trans
      change ((103860126036343 / 281474976710656 : ℚ) : ℝ) ≤ ((103860126036343 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (200 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_200.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_200.trans
      change ((25844009837705 / 70368744177664 : ℚ) : ℝ) ≤ ((103376039350820 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (201 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_201.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_201.trans
      change ((51445613720899 / 140737488355328 : ℚ) : ℝ) ≤ ((102891227441798 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (202 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_202.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_202.trans
      change ((25601422169585 / 70368744177664 : ℚ) : ℝ) ≤ ((102405688678340 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (203 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_203.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_203.trans
      change ((50959710712307 / 140737488355328 : ℚ) : ℝ) ≤ ((101919421424614 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (204 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_204.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_204.trans
      change ((101432424039877 / 281474976710656 : ℚ) : ℝ) ≤ ((101432424039877 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (205 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_205.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_205.trans
      change ((100944694878453 / 281474976710656 : ℚ) : ℝ) ≤ ((100944694878453 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (206 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_206.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_206.trans
      change ((50228116144859 / 140737488355328 : ℚ) : ℝ) ≤ ((100456232289718 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (207 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_207.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_207.trans
      change ((99967034618081 / 281474976710656 : ℚ) : ℝ) ≤ ((99967034618081 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (208 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_208.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_208.trans
      change ((99477100202963 / 281474976710656 : ℚ) : ℝ) ≤ ((99477100202963 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (209 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_209.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_209.trans
      change ((98986427378779 / 281474976710656 : ℚ) : ℝ) ≤ ((98986427378779 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (210 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_210.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_210.trans
      change ((98495014474921 / 281474976710656 : ℚ) : ℝ) ≤ ((98495014474921 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (211 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_211.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_211.trans
      change ((12250357476967 / 35184372088832 : ℚ) : ℝ) ≤ ((98002859815736 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (212 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_212.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_212.trans
      change ((48754980860255 / 140737488355328 : ℚ) : ℝ) ≤ ((97509961720510 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (213 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_213.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_213.trans
      change ((97016318503447 / 281474976710656 : ℚ) : ℝ) ≤ ((97016318503447 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (214 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_214.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_214.trans
      change ((48260964236825 / 140737488355328 : ℚ) : ℝ) ≤ ((96521928473650 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (215 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_215.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_215.trans
      change ((48013394967551 / 140737488355328 : ℚ) : ℝ) ≤ ((96026789935102 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (216 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_216.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_216.trans
      change ((95530901186647 / 281474976710656 : ℚ) : ℝ) ≤ ((95530901186647 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (217 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_217.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_217.trans
      change ((95034260521971 / 281474976710656 : ℚ) : ℝ) ≤ ((95034260521971 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (218 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_218.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_218.trans
      change ((47268433114789 / 140737488355328 : ℚ) : ℝ) ≤ ((94536866229578 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (219 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_219.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_219.trans
      change ((94038716592779 / 281474976710656 : ℚ) : ℝ) ≤ ((94038716592779 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (220 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_220.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_220.trans
      change ((93539809889661 / 281474976710656 : ℚ) : ℝ) ≤ ((93539809889661 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (221 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_221.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_221.trans
      change ((93040144393079 / 281474976710656 : ℚ) : ℝ) ≤ ((93040144393079 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (222 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_222.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_222.trans
      change ((92539718370627 / 281474976710656 : ℚ) : ℝ) ≤ ((92539718370627 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (223 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma006.sigma_factor_upper_223.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma006.sigma_power_upper_223.trans
      change ((46019265042311 / 140737488355328 : ℚ) : ℝ) ≤ ((92038530084622 : ℕ) : ℝ) / 2^48
      norm_num
end LegendreK6.M3Far.FactorBounds.Sigma006
