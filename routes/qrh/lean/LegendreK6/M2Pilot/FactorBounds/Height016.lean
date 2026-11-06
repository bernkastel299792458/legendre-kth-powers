import LegendreK6.M2Pilot.Enclosures.Height016
import LegendreK6.M2PilotIntegerData

/-! Join checked analytic enclosures to the exact dyadic witness table. -/
namespace LegendreK6.M2Pilot.FactorBounds.Height016
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem bounds (i : Fin 988) (hlo : 512 ≤ i.val) (hhi : i.val < 544) :
    heightFactor i ≤ heightDyadicFactor i ∧ heightPower i ≤ heightDyadicPower i := by
  interval_cases hi : i.val
  · have heq : i = (512 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height016.height_factor_upper_512.trans
      change ((319744526347 / 70368744177664 : ℚ) : ℝ) ≤ ((1278978105388 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height016.height_power_upper_512.trans
      change ((580233446172653 / 70368744177664 : ℚ) : ℝ) ≤ ((2320933784690612 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (513 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height016.height_factor_upper_513.trans
      change ((623668418859 / 140737488355328 : ℚ) : ℝ) ≤ ((1247336837718 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height016.height_power_upper_513.trans
      change ((36335177794817 / 4398046511104 : ℚ) : ℝ) ≤ ((2325451378868288 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (514 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height016.height_factor_upper_514.trans
      change ((1216477847155 / 281474976710656 : ℚ) : ℝ) ≤ ((1216477847155 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height016.height_power_upper_514.trans
      change ((582492230573349 / 70368744177664 : ℚ) : ℝ) ≤ ((2329968922293396 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (515 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height016.height_factor_upper_515.trans
      change ((1186381806307 / 281474976710656 : ℚ) : ℝ) ≤ ((1186381806307 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height016.height_power_upper_515.trans
      change ((2334486415009013 / 281474976710656 : ℚ) : ℝ) ≤ ((2334486415009013 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (516 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height016.height_factor_upper_516.trans
      change ((578514932481 / 140737488355328 : ℚ) : ℝ) ≤ ((1157029864962 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height016.height_power_upper_516.trans
      change ((1169501928529079 / 140737488355328 : ℚ) : ℝ) ≤ ((2339003857058158 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (517 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height016.height_factor_upper_517.trans
      change ((564201819157 / 140737488355328 : ℚ) : ℝ) ≤ ((1128403638314 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height016.height_power_upper_517.trans
      change ((585880312120949 / 70368744177664 : ℚ) : ℝ) ≤ ((2343521248483796 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (518 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height016.height_factor_upper_518.trans
      change ((137560649435 / 35184372088832 : ℚ) : ℝ) ≤ ((1100485195480 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height016.height_power_upper_518.trans
      change ((587009647332209 / 70368744177664 : ℚ) : ℝ) ≤ ((2348038589328836 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (519 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height016.height_factor_upper_519.trans
      change ((536628524151 / 140737488355328 : ℚ) : ℝ) ≤ ((1073257048302 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height016.height_power_upper_519.trans
      change ((294069484954517 / 35184372088832 : ℚ) : ℝ) ≤ ((2352555879636136 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (520 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height016.height_factor_upper_520.trans
      change ((1046702140423 / 281474976710656 : ℚ) : ℝ) ≤ ((1046702140423 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height016.height_power_upper_520.trans
      change ((2357073119448497 / 281474976710656 : ℚ) : ℝ) ≤ ((2357073119448497 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (521 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height016.height_factor_upper_521.trans
      change ((510401918317 / 140737488355328 : ℚ) : ℝ) ≤ ((1020803836634 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height016.height_power_upper_521.trans
      change ((295198788601083 / 35184372088832 : ℚ) : ℝ) ≤ ((2361590308808664 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (522 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height016.height_factor_upper_522.trans
      change ((995545912481 / 281474976710656 : ℚ) : ℝ) ≤ ((995545912481 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height016.height_power_upper_522.trans
      change ((2366107447759333 / 281474976710656 : ℚ) : ℝ) ≤ ((2366107447759333 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (523 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height016.height_factor_upper_523.trans
      change ((970912544131 / 281474976710656 : ℚ) : ℝ) ≤ ((970912544131 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height016.height_power_upper_523.trans
      change ((2370624536343139 / 281474976710656 : ℚ) : ℝ) ≤ ((2370624536343139 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (524 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height016.height_factor_upper_524.trans
      change ((946888298487 / 281474976710656 : ℚ) : ℝ) ≤ ((946888298487 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height016.height_power_upper_524.trans
      change ((1187570787301335 / 140737488355328 : ℚ) : ℝ) ≤ ((2375141574602670 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (525 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height016.height_factor_upper_525.trans
      change ((923458123549 / 281474976710656 : ℚ) : ℝ) ≤ ((923458123549 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height016.height_power_upper_525.trans
      change ((1189829281290227 / 140737488355328 : ℚ) : ℝ) ≤ ((2379658562580454 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (526 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height016.height_factor_upper_526.trans
      change ((900607339003 / 281474976710656 : ℚ) : ℝ) ≤ ((900607339003 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height016.height_power_upper_526.trans
      change ((2384175500318969 / 281474976710656 : ℚ) : ℝ) ≤ ((2384175500318969 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (527 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height016.height_factor_upper_527.trans
      change ((439160813529 / 140737488355328 : ℚ) : ℝ) ≤ ((878321627058 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height016.height_power_upper_527.trans
      change ((1194346193930319 / 140737488355328 : ℚ) : ℝ) ≤ ((2388692387860638 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (528 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height016.height_factor_upper_528.trans
      change ((428293511747 / 140737488355328 : ℚ) : ℝ) ≤ ((856587023494 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height016.height_power_upper_528.trans
      change ((2393209225247829 / 281474976710656 : ℚ) : ℝ) ≤ ((2393209225247829 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (529 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height016.height_factor_upper_529.trans
      change ((835389908939 / 281474976710656 : ℚ) : ℝ) ≤ ((835389908939 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height016.height_power_upper_529.trans
      change ((1198863006261429 / 140737488355328 : ℚ) : ℝ) ≤ ((2397726012522858 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (530 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height016.height_factor_upper_530.trans
      change ((407358500181 / 140737488355328 : ℚ) : ℝ) ≤ ((814717000362 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height016.height_power_upper_530.trans
      change ((600560687431997 / 70368744177664 : ℚ) : ℝ) ≤ ((2402242749727988 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (531 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height016.height_factor_upper_531.trans
      change ((397277671383 / 140737488355328 : ℚ) : ℝ) ≤ ((794555342766 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height016.height_power_upper_531.trans
      change ((1203379718452713 / 140737488355328 : ℚ) : ℝ) ≤ ((2406759436905426 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (532 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height016.height_factor_upper_532.trans
      change ((774892301101 / 281474976710656 : ℚ) : ℝ) ≤ ((774892301101 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height016.height_power_upper_532.trans
      change ((150704754631083 / 17592186044416 : ℚ) : ℝ) ≤ ((2411276074097328 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (533 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height016.height_factor_upper_533.trans
      change ((94464444045 / 35184372088832 : ℚ) : ℝ) ≤ ((755715552360 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height016.height_power_upper_533.trans
      change ((603948165336449 / 70368744177664 : ℚ) : ℝ) ≤ ((2415792661345796 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (534 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height016.height_factor_upper_534.trans
      change ((737013077883 / 281474976710656 : ℚ) : ℝ) ≤ ((737013077883 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height016.height_power_upper_534.trans
      change ((2420309198692879 / 281474976710656 : ℚ) : ℝ) ≤ ((2420309198692879 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (535 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height016.height_factor_upper_535.trans
      change ((718773155847 / 281474976710656 : ℚ) : ℝ) ≤ ((718773155847 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height016.height_power_upper_535.trans
      change ((606206421545143 / 70368744177664 : ℚ) : ℝ) ≤ ((2424825686180572 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (536 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height016.height_factor_upper_536.trans
      change ((350492176967 / 140737488355328 : ℚ) : ℝ) ≤ ((700984353934 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height016.height_power_upper_536.trans
      change ((1214671061925409 / 140737488355328 : ℚ) : ℝ) ≤ ((2429342123850818 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (537 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height016.height_factor_upper_537.trans
      change ((42727220137 / 17592186044416 : ℚ) : ℝ) ≤ ((683635522192 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height016.height_power_upper_537.trans
      change ((2433858511745507 / 281474976710656 : ℚ) : ℝ) ≤ ((2433858511745507 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (538 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height016.height_factor_upper_538.trans
      change ((666715786063 / 281474976710656 : ℚ) : ℝ) ≤ ((666715786063 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height016.height_power_upper_538.trans
      change ((2438374849906475 / 281474976710656 : ℚ) : ℝ) ≤ ((2438374849906475 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (539 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height016.height_factor_upper_539.trans
      change ((325107269793 / 140737488355328 : ℚ) : ℝ) ≤ ((650214539586 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height016.height_power_upper_539.trans
      change ((610722784593877 / 70368744177664 : ℚ) : ℝ) ≤ ((2442891138375508 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (540 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height016.height_factor_upper_540.trans
      change ((317060719383 / 140737488355328 : ℚ) : ℝ) ≤ ((634121438766 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height016.height_power_upper_540.trans
      change ((2447407377194337 / 281474976710656 : ℚ) : ℝ) ≤ ((2447407377194337 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (541 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height016.height_factor_upper_541.trans
      change ((618426395113 / 281474976710656 : ℚ) : ℝ) ≤ ((618426395113 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height016.height_power_upper_541.trans
      change ((2451923566404641 / 281474976710656 : ℚ) : ℝ) ≤ ((2451923566404641 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (542 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height016.height_factor_upper_542.trans
      change ((301559784665 / 140737488355328 : ℚ) : ℝ) ≤ ((603119569330 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height016.height_power_upper_542.trans
      change ((1228219853024023 / 140737488355328 : ℚ) : ℝ) ≤ ((2456439706048046 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (543 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height016.height_factor_upper_543.trans
      change ((147047841291 / 70368744177664 : ℚ) : ℝ) ≤ ((588191365164 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height016.height_power_upper_543.trans
      change ((2460955796166127 / 281474976710656 : ℚ) : ℝ) ≤ ((2460955796166127 : ℕ) : ℝ) / 2^48
      norm_num
end LegendreK6.M2Pilot.FactorBounds.Height016
