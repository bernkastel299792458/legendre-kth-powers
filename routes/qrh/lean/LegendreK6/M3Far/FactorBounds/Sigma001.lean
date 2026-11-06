import LegendreK6.M3Far.Enclosures.Sigma001
import LegendreK6.M3FarIntegerData

/-! Join checked analytic enclosures to the exact dyadic witness table. -/
namespace LegendreK6.M3Far.FactorBounds.Sigma001
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem bounds (i : Fin 384) (hlo : 32 ≤ i.val) (hhi : i.val < 64) :
    sigmaFactor i ≤ sigmaDyadicFactor i ∧ sigmaPower i ≤ sigmaDyadicPower i := by
  interval_cases hi : i.val
  · have heq : i = (32 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_32.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_32.trans
      change ((175672325890339 / 281474976710656 : ℚ) : ℝ) ≤ ((175672325890339 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (33 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_33.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_33.trans
      change ((87644902927869 / 140737488355328 : ℚ) : ℝ) ≤ ((175289805855738 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (34 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_34.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_34.trans
      change ((174906776473555 / 281474976710656 : ℚ) : ℝ) ≤ ((174906776473555 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (35 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_35.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_35.trans
      change ((174523236725773 / 281474976710656 : ℚ) : ℝ) ≤ ((174523236725773 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (36 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_36.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_36.trans
      change ((43534796397915 / 70368744177664 : ℚ) : ℝ) ≤ ((174139185591660 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (37 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_37.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_37.trans
      change ((173754622047761 / 281474976710656 : ℚ) : ℝ) ≤ ((173754622047761 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (38 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_38.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_38.trans
      change ((86684772533945 / 140737488355328 : ℚ) : ℝ) ≤ ((173369545067890 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (39 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_39.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_39.trans
      change ((43245988405779 / 70368744177664 : ℚ) : ℝ) ≤ ((172983953623116 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (40 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_40.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_40.trans
      change ((172597846681757 / 281474976710656 : ℚ) : ℝ) ≤ ((172597846681757 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (41 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_41.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_41.trans
      change ((86105611604687 / 140737488355328 : ℚ) : ℝ) ≤ ((172211223209374 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (42 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_42.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_42.trans
      change ((85912041084377 / 140737488355328 : ℚ) : ℝ) ≤ ((171824082168754 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (43 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_43.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_43.trans
      change ((171436422519909 / 281474976710656 : ℚ) : ℝ) ≤ ((171436422519909 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (44 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_44.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_44.trans
      change ((42762060805015 / 70368744177664 : ℚ) : ℝ) ≤ ((171048243220060 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (45 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_45.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_45.trans
      change ((170659543223631 / 281474976710656 : ℚ) : ℝ) ≤ ((170659543223631 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (46 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_46.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_46.trans
      change ((170270321482241 / 281474976710656 : ℚ) : ℝ) ≤ ((170270321482241 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (47 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_47.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_47.trans
      change ((84940288472345 / 140737488355328 : ℚ) : ℝ) ≤ ((169880576944690 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (48 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_48.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_48.trans
      change ((169490308556955 / 281474976710656 : ℚ) : ℝ) ≤ ((169490308556955 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (49 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_49.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_49.trans
      change ((84549757631087 / 140737488355328 : ℚ) : ℝ) ≤ ((169099515262174 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (50 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_50.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_50.trans
      change ((168708196000645 / 281474976710656 : ℚ) : ℝ) ≤ ((168708196000645 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (51 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_51.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_51.trans
      change ((168316349709807 / 281474976710656 : ℚ) : ℝ) ≤ ((168316349709807 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (52 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_52.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_52.trans
      change ((167923975324237 / 281474976710656 : ℚ) : ℝ) ≤ ((167923975324237 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (53 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_53.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_53.trans
      change ((167531071775639 / 281474976710656 : ℚ) : ℝ) ≤ ((167531071775639 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (54 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_54.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_54.trans
      change ((167137637992833 / 281474976710656 : ℚ) : ℝ) ≤ ((167137637992833 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (55 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_55.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_55.trans
      change ((10421479556359 / 17592186044416 : ℚ) : ℝ) ≤ ((166743672901744 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (56 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_56.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_56.trans
      change ((166349175425397 / 281474976710656 : ℚ) : ℝ) ≤ ((166349175425397 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (57 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_57.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_57.trans
      change ((165954144483903 / 281474976710656 : ℚ) : ℝ) ≤ ((165954144483903 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (58 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_58.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_58.trans
      change ((82779289497225 / 140737488355328 : ℚ) : ℝ) ≤ ((165558578994450 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (59 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_59.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_59.trans
      change ((165162477871295 / 281474976710656 : ℚ) : ℝ) ≤ ((165162477871295 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (60 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_60.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_60.trans
      change ((82382920012875 / 140737488355328 : ℚ) : ℝ) ≤ ((164765840025750 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (61 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_61.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_61.trans
      change ((82184332183089 / 140737488355328 : ℚ) : ℝ) ≤ ((164368664366178 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (62 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_62.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_62.trans
      change ((20496368724747 / 35184372088832 : ℚ) : ℝ) ≤ ((163970949797976 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (63 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma001.sigma_factor_upper_63.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma001.sigma_power_upper_63.trans
      change ((40893173805893 / 70368744177664 : ℚ) : ℝ) ≤ ((163572695223572 : ℕ) : ℝ) / 2^48
      norm_num
end LegendreK6.M3Far.FactorBounds.Sigma001
