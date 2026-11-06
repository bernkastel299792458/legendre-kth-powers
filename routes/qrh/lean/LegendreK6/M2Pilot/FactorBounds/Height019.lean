import LegendreK6.M2Pilot.Enclosures.Height019
import LegendreK6.M2PilotIntegerData

/-! Join checked analytic enclosures to the exact dyadic witness table. -/
namespace LegendreK6.M2Pilot.FactorBounds.Height019
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem bounds (i : Fin 988) (hlo : 608 ≤ i.val) (hhi : i.val < 640) :
    heightFactor i ≤ heightDyadicFactor i ∧ heightPower i ≤ heightDyadicPower i := by
  interval_cases hi : i.val
  · have heq : i = (608 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height019.height_factor_upper_608.trans
      change ((57623937123 / 140737488355328 : ℚ) : ℝ) ≤ ((115247874246 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height019.height_power_upper_608.trans
      change ((2754397371950053 / 281474976710656 : ℚ) : ℝ) ≤ ((2754397371950053 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (609 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height019.height_factor_upper_609.trans
      change ((112392338397 / 281474976710656 : ℚ) : ℝ) ≤ ((112392338397 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height019.height_power_upper_609.trans
      change ((2758910282766653 / 281474976710656 : ℚ) : ℝ) ≤ ((2758910282766653 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (610 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height019.height_factor_upper_610.trans
      change ((13700939075 / 35184372088832 : ℚ) : ℝ) ≤ ((109607512600 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height019.height_power_upper_610.trans
      change ((690855786682137 / 70368744177664 : ℚ) : ℝ) ≤ ((2763423146728548 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (611 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height019.height_factor_upper_611.trans
      change ((6680727937 / 17592186044416 : ℚ) : ℝ) ≤ ((106891646992 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height019.height_power_upper_611.trans
      change ((691983990968487 / 70368744177664 : ℚ) : ℝ) ≤ ((2767935963873948 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (612 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height019.height_factor_upper_612.trans
      change ((52121517491 / 140737488355328 : ℚ) : ℝ) ≤ ((104243034982 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height019.height_power_upper_612.trans
      change ((2772448734241015 / 281474976710656 : ℚ) : ℝ) ≤ ((2772448734241015 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (613 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height019.height_factor_upper_613.trans
      change ((101660012191 / 281474976710656 : ℚ) : ℝ) ≤ ((101660012191 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height019.height_power_upper_613.trans
      change ((694240364466967 / 70368744177664 : ℚ) : ℝ) ≤ ((2776961457867868 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (614 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height019.height_factor_upper_614.trans
      change ((49570477699 / 140737488355328 : ℚ) : ℝ) ≤ ((99140955398 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height019.height_power_upper_614.trans
      change ((1390737067396287 / 140737488355328 : ℚ) : ℝ) ≤ ((2781474134792574 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (615 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height019.height_factor_upper_615.trans
      change ((24171070383 / 70368744177664 : ℚ) : ℝ) ≤ ((96684281532 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height019.height_power_upper_615.trans
      change ((1392993382526579 / 140737488355328 : ℚ) : ℝ) ≤ ((2785986765053158 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (616 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height019.height_factor_upper_616.trans
      change ((94288446675 / 281474976710656 : ℚ) : ℝ) ≤ ((94288446675 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height019.height_power_upper_616.trans
      change ((2790499348687597 / 281474976710656 : ℚ) : ℝ) ≤ ((2790499348687597 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (617 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height019.height_factor_upper_617.trans
      change ((91951945093 / 281474976710656 : ℚ) : ℝ) ≤ ((91951945093 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height019.height_power_upper_617.trans
      change ((698752971433455 / 70368744177664 : ℚ) : ℝ) ≤ ((2795011885733820 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (618 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height019.height_factor_upper_618.trans
      change ((11209163537 / 35184372088832 : ℚ) : ℝ) ≤ ((89673308296 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height019.height_power_upper_618.trans
      change ((2799524376229713 / 281474976710656 : ℚ) : ℝ) ≤ ((2799524376229713 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (619 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height019.height_factor_upper_619.trans
      change ((87451104115 / 281474976710656 : ℚ) : ℝ) ≤ ((87451104115 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height019.height_power_upper_619.trans
      change ((1402018410106557 / 140737488355328 : ℚ) : ℝ) ≤ ((2804036820213114 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (620 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height019.height_factor_upper_620.trans
      change ((42641967903 / 140737488355328 : ℚ) : ℝ) ≤ ((85283935806 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height019.height_power_upper_620.trans
      change ((2808549217721813 / 281474976710656 : ℚ) : ℝ) ≤ ((2808549217721813 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (621 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height019.height_factor_upper_621.trans
      change ((20792610293 / 70368744177664 : ℚ) : ℝ) ≤ ((83170441172 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height019.height_power_upper_621.trans
      change ((1406530784396779 / 140737488355328 : ℚ) : ℝ) ≤ ((2813061568793558 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (622 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height019.height_factor_upper_622.trans
      change ((81109291711 / 281474976710656 : ℚ) : ℝ) ≤ ((81109291711 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height019.height_power_upper_622.trans
      change ((2817573873466049 / 281474976710656 : ℚ) : ℝ) ≤ ((2817573873466049 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (623 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height019.height_factor_upper_623.trans
      change ((39549595891 / 140737488355328 : ℚ) : ℝ) ≤ ((79099191782 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height019.height_power_upper_623.trans
      change ((2822086131776939 / 281474976710656 : ℚ) : ℝ) ≤ ((2822086131776939 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (624 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height019.height_factor_upper_624.trans
      change ((38569438897 / 140737488355328 : ℚ) : ℝ) ≤ ((77138877794 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height019.height_power_upper_624.trans
      change ((2826598343763837 / 281474976710656 : ℚ) : ℝ) ≤ ((2826598343763837 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (625 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height019.height_factor_upper_625.trans
      change ((75227117411 / 281474976710656 : ℚ) : ℝ) ≤ ((75227117411 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height019.height_power_upper_625.trans
      change ((2831110509464305 / 281474976710656 : ℚ) : ℝ) ≤ ((2831110509464305 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (626 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height019.height_factor_upper_626.trans
      change ((73362708783 / 281474976710656 : ℚ) : ℝ) ≤ ((73362708783 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height019.height_power_upper_626.trans
      change ((708905657228965 / 70368744177664 : ℚ) : ℝ) ≤ ((2835622628915860 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (627 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height019.height_factor_upper_627.trans
      change ((71544479789 / 281474976710656 : ℚ) : ℝ) ≤ ((71544479789 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height019.height_power_upper_627.trans
      change ((2840134702155973 / 281474976710656 : ℚ) : ℝ) ≤ ((2840134702155973 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (628 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height019.height_factor_upper_628.trans
      change ((34885643653 / 140737488355328 : ℚ) : ℝ) ≤ ((69771287306 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height019.height_power_upper_628.trans
      change ((2844646729222071 / 281474976710656 : ℚ) : ℝ) ≤ ((2844646729222071 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (629 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height019.height_factor_upper_629.trans
      change ((8505252061 / 35184372088832 : ℚ) : ℝ) ≤ ((68042016488 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height019.height_power_upper_629.trans
      change ((2849158710151533 / 281474976710656 : ℚ) : ℝ) ≤ ((2849158710151533 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (630 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height019.height_factor_upper_630.trans
      change ((16588895017 / 70368744177664 : ℚ) : ℝ) ≤ ((66355580068 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height019.height_power_upper_630.trans
      change ((2853670644981695 / 281474976710656 : ℚ) : ℝ) ≤ ((2853670644981695 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (631 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height019.height_factor_upper_631.trans
      change ((64710917679 / 281474976710656 : ℚ) : ℝ) ≤ ((64710917679 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height019.height_power_upper_631.trans
      change ((2858182533749845 / 281474976710656 : ℚ) : ℝ) ≤ ((2858182533749845 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (632 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height019.height_factor_upper_632.trans
      change ((63106995185 / 281474976710656 : ℚ) : ℝ) ≤ ((63106995185 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height019.height_power_upper_632.trans
      change ((2862694376493229 / 281474976710656 : ℚ) : ℝ) ≤ ((2862694376493229 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (633 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height019.height_factor_upper_633.trans
      change ((15385701009 / 70368744177664 : ℚ) : ℝ) ≤ ((61542804036 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height019.height_power_upper_633.trans
      change ((1433603086624523 / 140737488355328 : ℚ) : ℝ) ≤ ((2867206173249046 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (634 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height019.height_factor_upper_634.trans
      change ((7502170079 / 35184372088832 : ℚ) : ℝ) ≤ ((60017360632 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height019.height_power_upper_634.trans
      change ((2871717924054449 / 281474976710656 : ℚ) : ℝ) ≤ ((2871717924054449 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (635 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height019.height_factor_upper_635.trans
      change ((58529705709 / 281474976710656 : ℚ) : ℝ) ≤ ((58529705709 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height019.height_power_upper_635.trans
      change ((2876229628946549 / 281474976710656 : ℚ) : ℝ) ≤ ((2876229628946549 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (636 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height019.height_factor_upper_636.trans
      change ((57078903737 / 281474976710656 : ℚ) : ℝ) ≤ ((57078903737 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height019.height_power_upper_636.trans
      change ((360092660995301 / 35184372088832 : ℚ) : ℝ) ≤ ((2880741287962408 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (637 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height019.height_factor_upper_637.trans
      change ((55664042329 / 281474976710656 : ℚ) : ℝ) ≤ ((55664042329 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height019.height_power_upper_637.trans
      change ((360656612642381 / 35184372088832 : ℚ) : ℝ) ≤ ((2885252901139048 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (638 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height019.height_factor_upper_638.trans
      change ((13571057919 / 70368744177664 : ℚ) : ℝ) ≤ ((54284231676 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height019.height_power_upper_638.trans
      change ((2889764468513441 / 281474976710656 : ℚ) : ℝ) ≤ ((2889764468513441 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (639 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height019.height_factor_upper_639.trans
      change ((52938603983 / 281474976710656 : ℚ) : ℝ) ≤ ((52938603983 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height019.height_power_upper_639.trans
      change ((1447137995061259 / 140737488355328 : ℚ) : ℝ) ≤ ((2894275990122518 : ℕ) : ℝ) / 2^48
      norm_num
end LegendreK6.M2Pilot.FactorBounds.Height019
