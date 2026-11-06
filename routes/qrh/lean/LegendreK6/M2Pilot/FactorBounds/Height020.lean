import LegendreK6.M2Pilot.Enclosures.Height020
import LegendreK6.M2PilotIntegerData

/-! Join checked analytic enclosures to the exact dyadic witness table. -/
namespace LegendreK6.M2Pilot.FactorBounds.Height020
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem bounds (i : Fin 988) (hlo : 640 ≤ i.val) (hhi : i.val < 672) :
    heightFactor i ≤ heightDyadicFactor i ∧ heightPower i ≤ heightDyadicPower i := by
  interval_cases hi : i.val
  · have heq : i = (640 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height020.height_factor_upper_640.trans
      change ((51626312927 / 281474976710656 : ℚ) : ℝ) ≤ ((51626312927 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height020.height_power_upper_640.trans
      change ((2898787466003165 / 281474976710656 : ℚ) : ℝ) ≤ ((2898787466003165 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (641 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height020.height_factor_upper_641.trans
      change ((25173266563 / 140737488355328 : ℚ) : ℝ) ≤ ((50346533126 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height020.height_power_upper_641.trans
      change ((2903298896192221 / 281474976710656 : ℚ) : ℝ) ≤ ((2903298896192221 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (642 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height020.height_factor_upper_642.trans
      change ((49098459619 / 281474976710656 : ℚ) : ℝ) ≤ ((49098459619 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height020.height_power_upper_642.trans
      change ((726952570181621 / 70368744177664 : ℚ) : ℝ) ≤ ((2907810280726484 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (643 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height020.height_factor_upper_643.trans
      change ((23940653683 / 140737488355328 : ℚ) : ℝ) ≤ ((47881307366 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height020.height_power_upper_643.trans
      change ((182020101227669 / 17592186044416 : ℚ) : ℝ) ≤ ((2912321619642704 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (644 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height020.height_factor_upper_644.trans
      change ((46694310749 / 281474976710656 : ℚ) : ℝ) ≤ ((46694310749 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height020.height_power_upper_644.trans
      change ((2916832912977589 / 281474976710656 : ℚ) : ℝ) ≤ ((2916832912977589 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (645 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height020.height_factor_upper_645.trans
      change ((22768361549 / 140737488355328 : ℚ) : ℝ) ≤ ((45536723098 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height020.height_power_upper_645.trans
      change ((1460672080383901 / 140737488355328 : ℚ) : ℝ) ≤ ((2921344160767802 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (646 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height020.height_factor_upper_646.trans
      change ((44407816217 / 281474976710656 : ℚ) : ℝ) ≤ ((44407816217 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height020.height_power_upper_646.trans
      change ((2925855363049961 / 281474976710656 : ℚ) : ℝ) ≤ ((2925855363049961 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (647 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height020.height_factor_upper_647.trans
      change ((21653439965 / 140737488355328 : ℚ) : ℝ) ≤ ((43306879930 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height020.height_power_upper_647.trans
      change ((2930366519860643 / 281474976710656 : ℚ) : ℝ) ≤ ((2930366519860643 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (648 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height020.height_factor_upper_648.trans
      change ((42233221637 / 281474976710656 : ℚ) : ℝ) ≤ ((42233221637 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height020.height_power_upper_648.trans
      change ((366859703904547 / 35184372088832 : ℚ) : ℝ) ≤ ((2934877631236376 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (649 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height020.height_factor_upper_649.trans
      change ((41186165875 / 281474976710656 : ℚ) : ℝ) ≤ ((41186165875 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height020.height_power_upper_649.trans
      change ((2939388697213649 / 281474976710656 : ℚ) : ℝ) ≤ ((2939388697213649 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (650 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height020.height_factor_upper_650.trans
      change ((20082526949 / 140737488355328 : ℚ) : ℝ) ≤ ((40165053898 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height020.height_power_upper_650.trans
      change ((2943899717828903 / 281474976710656 : ℚ) : ℝ) ≤ ((2943899717828903 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (651 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height020.height_factor_upper_651.trans
      change ((9792310815 / 70368744177664 : ℚ) : ℝ) ≤ ((39169243260 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height020.height_power_upper_651.trans
      change ((2948410693118537 / 281474976710656 : ℚ) : ℝ) ≤ ((2948410693118537 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (652 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height020.height_factor_upper_652.trans
      change ((38198107417 / 281474976710656 : ℚ) : ℝ) ≤ ((38198107417 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height020.height_power_upper_652.trans
      change ((1476460811559453 / 140737488355328 : ℚ) : ℝ) ≤ ((2952921623118906 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (653 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height020.height_factor_upper_653.trans
      change ((582047427 / 4398046511104 : ℚ) : ℝ) ≤ ((37251035328 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height020.height_power_upper_653.trans
      change ((1478716253933161 / 140737488355328 : ℚ) : ℝ) ≤ ((2957432507866322 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (654 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height020.height_factor_upper_654.trans
      change ((36327431077 / 281474976710656 : ℚ) : ℝ) ≤ ((36327431077 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height020.height_power_upper_654.trans
      change ((740485836849263 / 70368744177664 : ℚ) : ℝ) ≤ ((2961943347397052 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (655 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height020.height_factor_upper_655.trans
      change ((8856678373 / 70368744177664 : ℚ) : ℝ) ≤ ((35426713492 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height020.height_power_upper_655.trans
      change ((2966454141747321 / 281474976710656 : ℚ) : ℝ) ≤ ((2966454141747321 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (656 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height020.height_factor_upper_656.trans
      change ((34548315789 / 281474976710656 : ℚ) : ℝ) ≤ ((34548315789 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height020.height_power_upper_656.trans
      change ((742741222738327 / 70368744177664 : ℚ) : ℝ) ≤ ((2970964890953308 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (657 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height020.height_factor_upper_657.trans
      change ((33691685209 / 281474976710656 : ℚ) : ℝ) ≤ ((33691685209 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height020.height_power_upper_657.trans
      change ((2975475595051151 / 281474976710656 : ℚ) : ℝ) ≤ ((2975475595051151 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (658 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height020.height_factor_upper_658.trans
      change ((16428141337 / 140737488355328 : ℚ) : ℝ) ≤ ((32856282674 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height020.height_power_upper_658.trans
      change ((186249140879809 / 17592186044416 : ℚ) : ℝ) ≤ ((2979986254076944 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (659 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height020.height_factor_upper_659.trans
      change ((16020791225 / 140737488355328 : ℚ) : ℝ) ≤ ((32041582450 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height020.height_power_upper_659.trans
      change ((1492248434033369 / 140737488355328 : ℚ) : ℝ) ≤ ((2984496868066738 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (660 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height020.height_factor_upper_660.trans
      change ((15623535907 / 140737488355328 : ℚ) : ℝ) ≤ ((31247071814 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height020.height_power_upper_660.trans
      change ((1494503718528269 / 140737488355328 : ℚ) : ℝ) ≤ ((2989007437056538 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (661 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height020.height_factor_upper_661.trans
      change ((30472250733 / 281474976710656 : ℚ) : ℝ) ≤ ((30472250733 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height020.height_power_upper_661.trans
      change ((1496758980541155 / 140737488355328 : ℚ) : ℝ) ≤ ((2993517961082310 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (662 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height020.height_factor_upper_662.trans
      change ((29716631551 / 281474976710656 : ℚ) : ℝ) ≤ ((29716631551 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height020.height_power_upper_662.trans
      change ((1499014220089987 / 140737488355328 : ℚ) : ℝ) ≤ ((2998028440179974 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (663 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height020.height_factor_upper_663.trans
      change ((7244934671 / 70368744177664 : ℚ) : ℝ) ≤ ((28979738684 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height020.height_power_upper_663.trans
      change ((2932166869517 / 274877906944 : ℚ) : ℝ) ≤ ((3002538874385408 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (664 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height020.height_factor_upper_664.trans
      change ((14130554159 / 140737488355328 : ℚ) : ℝ) ≤ ((28261108318 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height020.height_power_upper_664.trans
      change ((187940578983403 / 17592186044416 : ℚ) : ℝ) ≤ ((3007049263734448 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (665 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height020.height_factor_upper_665.trans
      change ((3445036015 / 35184372088832 : ℚ) : ℝ) ≤ ((27560288120 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height020.height_power_upper_665.trans
      change ((752889902065721 / 70368744177664 : ℚ) : ℝ) ≤ ((3011559608262884 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (666 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height020.height_factor_upper_666.trans
      change ((13438418477 / 140737488355328 : ℚ) : ℝ) ≤ ((26876836954 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height020.height_power_upper_666.trans
      change ((3016069908006467 / 281474976710656 : ℚ) : ℝ) ≤ ((3016069908006467 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (667 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height020.height_factor_upper_667.trans
      change ((6552581151 / 70368744177664 : ℚ) : ℝ) ≤ ((26210324604 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height020.height_power_upper_667.trans
      change ((3020580163000903 / 281474976710656 : ℚ) : ℝ) ≤ ((3020580163000903 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (668 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height020.height_factor_upper_668.trans
      change ((25560331503 / 281474976710656 : ℚ) : ℝ) ≤ ((25560331503 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height020.height_power_upper_668.trans
      change ((47267037082529 / 4398046511104 : ℚ) : ℝ) ≤ ((3025090373281856 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (669 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height020.height_factor_upper_669.trans
      change ((12463224235 / 140737488355328 : ℚ) : ℝ) ≤ ((24926448470 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height020.height_power_upper_669.trans
      change ((3029600538884947 / 281474976710656 : ℚ) : ℝ) ≤ ((3029600538884947 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (670 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height020.height_factor_upper_670.trans
      change ((12154138227 / 140737488355328 : ℚ) : ℝ) ≤ ((24308276454 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height020.height_power_upper_670.trans
      change ((1517055329922877 / 140737488355328 : ℚ) : ℝ) ≤ ((3034110659845754 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (671 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height020.height_factor_upper_671.trans
      change ((11852713141 / 140737488355328 : ℚ) : ℝ) ≤ ((23705426282 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height020.height_power_upper_671.trans
      change ((3038620736199813 / 281474976710656 : ℚ) : ℝ) ≤ ((3038620736199813 : ℕ) : ℝ) / 2^48
      norm_num
end LegendreK6.M2Pilot.FactorBounds.Height020
