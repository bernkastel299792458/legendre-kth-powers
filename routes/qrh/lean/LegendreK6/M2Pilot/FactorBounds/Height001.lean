import LegendreK6.M2Pilot.Enclosures.Height001
import LegendreK6.M2PilotIntegerData

/-! Join checked analytic enclosures to the exact dyadic witness table. -/
namespace LegendreK6.M2Pilot.FactorBounds.Height001
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem bounds (i : Fin 988) (hlo : 32 ≤ i.val) (hhi : i.val < 64) :
    heightFactor i ≤ heightDyadicFactor i ∧ heightPower i ≤ heightDyadicPower i := by
  interval_cases hi : i.val
  · have heq : i = (32 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height001.height_factor_upper_32.trans
      change ((1349479967396157 / 70368744177664 : ℚ) : ℝ) ≤ ((5397919869584628 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height001.height_power_upper_32.trans
      change ((145683673448587 / 281474976710656 : ℚ) : ℝ) ≤ ((145683673448587 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (33 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height001.height_factor_upper_33.trans
      change ((2674318547269489 / 140737488355328 : ℚ) : ℝ) ≤ ((5348637094538978 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height001.height_power_upper_33.trans
      change ((75115939996753 / 140737488355328 : ℚ) : ℝ) ≤ ((150231879993506 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (34 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height001.height_factor_upper_34.trans
      change ((5299800751599845 / 281474976710656 : ℚ) : ℝ) ≤ ((5299800751599845 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height001.height_power_upper_34.trans
      change ((38695001618605 / 70368744177664 : ℚ) : ℝ) ≤ ((154780006474420 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (35 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height001.height_factor_upper_35.trans
      change ((2625703416406165 / 140737488355328 : ℚ) : ℝ) ≤ ((5251406832812330 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height001.height_power_upper_35.trans
      change ((159328052976663 / 281474976710656 : ℚ) : ℝ) ≤ ((159328052976663 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (36 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height001.height_factor_upper_36.trans
      change ((5203451365833405 / 281474976710656 : ℚ) : ℝ) ≤ ((5203451365833405 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height001.height_power_upper_36.trans
      change ((20484502448179 / 35184372088832 : ℚ) : ℝ) ≤ ((163876019585432 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (37 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height001.height_factor_upper_37.trans
      change ((2577965206809647 / 140737488355328 : ℚ) : ℝ) ≤ ((5155930413619294 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height001.height_power_upper_37.trans
      change ((168423906385787 / 281474976710656 : ℚ) : ℝ) ≤ ((168423906385787 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (38 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height001.height_factor_upper_38.trans
      change ((1277210018528893 / 70368744177664 : ℚ) : ℝ) ≤ ((5108840074115572 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height001.height_power_upper_38.trans
      change ((172971713462653 / 281474976710656 : ℚ) : ℝ) ≤ ((172971713462653 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (39 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height001.height_factor_upper_39.trans
      change ((2531088239974967 / 140737488355328 : ℚ) : ℝ) ≤ ((5062176479949934 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height001.height_power_upper_39.trans
      change ((177519440900821 / 281474976710656 : ℚ) : ℝ) ≤ ((177519440900821 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (40 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height001.height_factor_upper_40.trans
      change ((2507967899063817 / 140737488355328 : ℚ) : ℝ) ≤ ((5015935798127634 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height001.height_power_upper_40.trans
      change ((182067088784945 / 281474976710656 : ℚ) : ℝ) ≤ ((182067088784945 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (41 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height001.height_factor_upper_41.trans
      change ((2485057114864775 / 140737488355328 : ℚ) : ℝ) ≤ ((4970114229729550 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height001.height_power_upper_41.trans
      change ((23326832149943 / 35184372088832 : ℚ) : ℝ) ≤ ((186614657199544 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (42 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height001.height_factor_upper_42.trans
      change ((4924708009612869 / 281474976710656 : ℚ) : ℝ) ≤ ((4924708009612869 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height001.height_power_upper_42.trans
      change ((191162146229003 / 281474976710656 : ℚ) : ℝ) ≤ ((191162146229003 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (43 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height001.height_factor_upper_43.trans
      change ((2439856703057183 / 140737488355328 : ℚ) : ℝ) ≤ ((4879713406114366 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height001.height_power_upper_43.trans
      change ((97854777978787 / 140737488355328 : ℚ) : ℝ) ≤ ((195709555957574 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (44 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height001.height_factor_upper_44.trans
      change ((4835126720756247 / 281474976710656 : ℚ) : ℝ) ≤ ((4835126720756247 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height001.height_power_upper_44.trans
      change ((50064221617343 / 70368744177664 : ℚ) : ℝ) ≤ ((200256886469372 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (45 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height001.height_factor_upper_45.trans
      change ((299434017997159 / 17592186044416 : ℚ) : ℝ) ≤ ((4790944287954544 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height001.height_power_upper_45.trans
      change ((51201034462095 / 70368744177664 : ℚ) : ℝ) ≤ ((204804137848380 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (46 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height001.height_factor_upper_46.trans
      change ((1186790618682509 / 70368744177664 : ℚ) : ℝ) ≤ ((4747162474730036 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height001.height_power_upper_46.trans
      change ((13084456886153 / 17592186044416 : ℚ) : ℝ) ≤ ((209351310178448 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (47 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height001.height_factor_upper_47.trans
      change ((4703777680421671 / 281474976710656 : ℚ) : ℝ) ≤ ((4703777680421671 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height001.height_power_upper_47.trans
      change ((53474600885823 / 70368744177664 : ℚ) : ℝ) ≤ ((213898403543292 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (48 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height001.height_factor_upper_48.trans
      change ((4660786336402475 / 281474976710656 : ℚ) : ℝ) ≤ ((4660786336402475 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height001.height_power_upper_48.trans
      change ((218445418026495 / 281474976710656 : ℚ) : ℝ) ≤ ((218445418026495 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (49 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height001.height_factor_upper_49.trans
      change ((4618184905797927 / 281474976710656 : ℚ) : ℝ) ≤ ((4618184905797927 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height001.height_power_upper_49.trans
      change ((222992353711507 / 281474976710656 : ℚ) : ℝ) ≤ ((222992353711507 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (50 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height001.height_factor_upper_50.trans
      change ((4575969883206763 / 281474976710656 : ℚ) : ℝ) ≤ ((4575969883206763 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height001.height_power_upper_50.trans
      change ((227539210681647 / 281474976710656 : ℚ) : ℝ) ≤ ((227539210681647 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (51 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height001.height_factor_upper_51.trans
      change ((2267068897212107 / 140737488355328 : ℚ) : ℝ) ≤ ((4534137794424214 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height001.height_power_upper_51.trans
      change ((232085989020101 / 281474976710656 : ℚ) : ℝ) ≤ ((232085989020101 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (52 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height001.height_factor_upper_52.trans
      change ((4492685196167635 / 281474976710656 : ℚ) : ℝ) ≤ ((4492685196167635 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height001.height_power_upper_52.trans
      change ((236632688809923 / 281474976710656 : ℚ) : ℝ) ≤ ((236632688809923 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (53 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height001.height_factor_upper_53.trans
      change ((4451608675804521 / 281474976710656 : ℚ) : ℝ) ≤ ((4451608675804521 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height001.height_power_upper_53.trans
      change ((241179310134037 / 281474976710656 : ℚ) : ℝ) ≤ ((241179310134037 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (54 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height001.height_factor_upper_54.trans
      change ((4410904851082869 / 281474976710656 : ℚ) : ℝ) ≤ ((4410904851082869 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height001.height_power_upper_54.trans
      change ((7678932908601 / 8796093022208 : ℚ) : ℝ) ≤ ((245725853075232 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (55 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height001.height_factor_upper_55.trans
      change ((4370570369863897 / 281474976710656 : ℚ) : ℝ) ≤ ((4370570369863897 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height001.height_power_upper_55.trans
      change ((62568079429043 / 70368744177664 : ℚ) : ℝ) ≤ ((250272317716172 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (56 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height001.height_factor_upper_56.trans
      change ((4330601909857065 / 281474976710656 : ℚ) : ℝ) ≤ ((4330601909857065 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height001.height_power_upper_56.trans
      change ((31852338017423 / 35184372088832 : ℚ) : ℝ) ≤ ((254818704139384 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (57 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height001.height_factor_upper_57.trans
      change ((4290996178357407 / 281474976710656 : ℚ) : ℝ) ≤ ((4290996178357407 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height001.height_power_upper_57.trans
      change ((259365012427269 / 281474976710656 : ℚ) : ℝ) ≤ ((259365012427269 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (58 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height001.height_factor_upper_58.trans
      change ((4251749911985137 / 281474976710656 : ℚ) : ℝ) ≤ ((4251749911985137 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height001.height_power_upper_58.trans
      change ((16494452666381 / 17592186044416 : ℚ) : ℝ) ≤ ((263911242662096 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (59 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height001.height_factor_upper_59.trans
      change ((2106429938213759 / 140737488355328 : ℚ) : ℝ) ≤ ((4212859876427518 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height001.height_power_upper_59.trans
      change ((67114348731501 / 70368744177664 : ℚ) : ℝ) ≤ ((268457394926004 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (60 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height001.height_factor_upper_60.trans
      change ((2087161433091483 / 140737488355328 : ℚ) : ℝ) ≤ ((4174322866182966 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height001.height_power_upper_60.trans
      change ((68250867325251 / 70368744177664 : ℚ) : ℝ) ≤ ((273003469301004 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (61 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height001.height_factor_upper_61.trans
      change ((2068067852153693 / 140737488355328 : ℚ) : ℝ) ≤ ((4136135704307386 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height001.height_power_upper_61.trans
      change ((17346841616811 / 17592186044416 : ℚ) : ℝ) ≤ ((277549465868976 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (62 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height001.height_factor_upper_62.trans
      change ((4098295242162701 / 281474976710656 : ℚ) : ℝ) ≤ ((4098295242162701 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height001.height_power_upper_62.trans
      change ((282095384711671 / 281474976710656 : ℚ) : ℝ) ≤ ((282095384711671 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (63 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height001.height_factor_upper_63.trans
      change ((4060798359167571 / 281474976710656 : ℚ) : ℝ) ≤ ((4060798359167571 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height001.height_power_upper_63.trans
      change ((286641225910713 / 281474976710656 : ℚ) : ℝ) ≤ ((286641225910713 : ℕ) : ℝ) / 2^48
      norm_num
end LegendreK6.M2Pilot.FactorBounds.Height001
