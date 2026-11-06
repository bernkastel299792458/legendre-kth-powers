import LegendreK6.M2Pilot.Enclosures.Height017
import LegendreK6.M2PilotIntegerData

/-! Join checked analytic enclosures to the exact dyadic witness table. -/
namespace LegendreK6.M2Pilot.FactorBounds.Height017
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem bounds (i : Fin 988) (hlo : 544 ≤ i.val) (hhi : i.val < 576) :
    heightFactor i ≤ heightDyadicFactor i ∧ heightPower i ≤ heightDyadicPower i := by
  interval_cases hi : i.val
  · have heq : i = (544 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height017.height_factor_upper_544.trans
      change ((573632423409 / 281474976710656 : ℚ) : ℝ) ≤ ((573632423409 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height017.height_power_upper_544.trans
      change ((2465471836800405 / 281474976710656 : ℚ) : ℝ) ≤ ((2465471836800405 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (545 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height017.height_factor_upper_545.trans
      change ((559433616051 / 281474976710656 : ℚ) : ℝ) ≤ ((559433616051 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height017.height_power_upper_545.trans
      change ((2469987827992351 / 281474976710656 : ℚ) : ℝ) ≤ ((2469987827992351 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (546 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height017.height_factor_upper_546.trans
      change ((272793020281 / 140737488355328 : ℚ) : ℝ) ≤ ((545586040562 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height017.height_power_upper_546.trans
      change ((1237251884891691 / 140737488355328 : ℚ) : ℝ) ≤ ((2474503769783382 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (547 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height017.height_factor_upper_547.trans
      change ((8313765849 / 4398046511104 : ℚ) : ℝ) ≤ ((532081014336 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height017.height_power_upper_547.trans
      change ((154938728888429 / 17592186044416 : ℚ) : ℝ) ≤ ((2479019662214864 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (548 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height017.height_factor_upper_548.trans
      change ((518910069259 / 281474976710656 : ℚ) : ℝ) ≤ ((518910069259 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height017.height_power_upper_548.trans
      change ((1241767752664055 / 140737488355328 : ℚ) : ℝ) ≤ ((2483535505328110 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (549 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height017.height_factor_upper_549.trans
      change ((506064946411 / 281474976710656 : ℚ) : ℝ) ≤ ((506064946411 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height017.height_power_upper_549.trans
      change ((1244025649582191 / 140737488355328 : ℚ) : ℝ) ≤ ((2488051299164382 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (550 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height017.height_factor_upper_550.trans
      change ((123384397727 / 70368744177664 : ℚ) : ℝ) ≤ ((493537590908 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height017.height_power_upper_550.trans
      change ((2492567043764891 / 281474976710656 : ℚ) : ℝ) ≤ ((2492567043764891 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (551 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height017.height_factor_upper_551.trans
      change ((481320146857 / 281474976710656 : ℚ) : ℝ) ≤ ((481320146857 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height017.height_power_upper_551.trans
      change ((2497082739170795 / 281474976710656 : ℚ) : ℝ) ≤ ((2497082739170795 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (552 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height017.height_factor_upper_552.trans
      change ((117351238113 / 70368744177664 : ℚ) : ℝ) ≤ ((469404952452 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height017.height_power_upper_552.trans
      change ((78174949544475 / 8796093022208 : ℚ) : ℝ) ≤ ((2501598385423200 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (553 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height017.height_factor_upper_553.trans
      change ((457784535175 / 281474976710656 : ℚ) : ℝ) ≤ ((457784535175 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height017.height_power_upper_553.trans
      change ((2506113982563163 / 281474976710656 : ℚ) : ℝ) ≤ ((2506113982563163 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (554 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height017.height_factor_upper_554.trans
      change ((446451607127 / 281474976710656 : ℚ) : ℝ) ≤ ((446451607127 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height017.height_power_upper_554.trans
      change ((1255314765315843 / 140737488355328 : ℚ) : ℝ) ≤ ((2510629530631686 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (555 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height017.height_factor_upper_555.trans
      change ((108849765117 / 70368744177664 : ℚ) : ℝ) ≤ ((435399060468 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height017.height_power_upper_555.trans
      change ((2515145029669723 / 281474976710656 : ℚ) : ℝ) ≤ ((2515145029669723 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (556 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height017.height_factor_upper_556.trans
      change ((212309981487 / 140737488355328 : ℚ) : ℝ) ≤ ((424619962974 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height017.height_power_upper_556.trans
      change ((2519660479718175 / 281474976710656 : ℚ) : ℝ) ≤ ((2519660479718175 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (557 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height017.height_factor_upper_557.trans
      change ((414107553697 / 281474976710656 : ℚ) : ℝ) ≤ ((414107553697 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height017.height_power_upper_557.trans
      change ((631043970204473 / 70368744177664 : ℚ) : ℝ) ≤ ((2524175880817892 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (558 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height017.height_factor_upper_558.trans
      change ((100963809685 / 70368744177664 : ℚ) : ℝ) ≤ ((403855238740 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height017.height_power_upper_558.trans
      change ((2528691233009673 / 281474976710656 : ℚ) : ℝ) ≤ ((2528691233009673 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (559 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height017.height_factor_upper_559.trans
      change ((393856587131 / 281474976710656 : ℚ) : ℝ) ≤ ((393856587131 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height017.height_power_upper_559.trans
      change ((1266603268167133 / 140737488355328 : ℚ) : ℝ) ≤ ((2533206536334266 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (560 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height017.height_factor_upper_560.trans
      change ((24006582925 / 17592186044416 : ℚ) : ℝ) ≤ ((384105326800 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height017.height_power_upper_560.trans
      change ((2537721790832369 / 281474976710656 : ℚ) : ℝ) ≤ ((2537721790832369 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (561 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height017.height_factor_upper_561.trans
      change ((187297670327 / 140737488355328 : ℚ) : ℝ) ≤ ((374595340654 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height017.height_power_upper_561.trans
      change ((635559249136157 / 70368744177664 : ℚ) : ℝ) ≤ ((2542236996544628 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (562 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height017.height_factor_upper_562.trans
      change ((365320662753 / 281474976710656 : ℚ) : ℝ) ≤ ((365320662753 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height017.height_power_upper_562.trans
      change ((2546752153511639 / 281474976710656 : ℚ) : ℝ) ≤ ((2546752153511639 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (563 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height017.height_factor_upper_563.trans
      change ((178137737289 / 140737488355328 : ℚ) : ℝ) ≤ ((356275474578 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height017.height_power_upper_563.trans
      change ((1275633630886973 / 140737488355328 : ℚ) : ℝ) ≤ ((2551267261773946 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (564 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height017.height_factor_upper_564.trans
      change ((173727050693 / 140737488355328 : ℚ) : ℝ) ≤ ((347454101386 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height017.height_power_upper_564.trans
      change ((638945580343011 / 70368744177664 : ℚ) : ℝ) ≤ ((2555782321372044 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (565 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height017.height_factor_upper_565.trans
      change ((42356376083 / 35184372088832 : ℚ) : ℝ) ≤ ((338851008664 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height017.height_power_upper_565.trans
      change ((2560297332346377 / 281474976710656 : ℚ) : ℝ) ≤ ((2560297332346377 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (566 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height017.height_factor_upper_566.trans
      change ((82615199667 / 70368744177664 : ℚ) : ℝ) ≤ ((330460798668 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height017.height_power_upper_566.trans
      change ((2564812294737339 / 281474976710656 : ℚ) : ℝ) ≤ ((2564812294737339 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (567 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height017.height_factor_upper_567.trans
      change ((161139103519 / 140737488355328 : ℚ) : ℝ) ≤ ((322278207038 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height017.height_power_upper_567.trans
      change ((321165901073159 / 35184372088832 : ℚ) : ℝ) ≤ ((2569327208585272 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (568 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height017.height_factor_upper_568.trans
      change ((39287262439 / 35184372088832 : ℚ) : ℝ) ≤ ((314298099512 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height017.height_power_upper_568.trans
      change ((2573842073930471 / 281474976710656 : ℚ) : ℝ) ≤ ((2573842073930471 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (569 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height017.height_factor_upper_569.trans
      change ((76628867177 / 70368744177664 : ℚ) : ℝ) ≤ ((306515468708 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height017.height_power_upper_569.trans
      change ((2578356890813177 / 281474976710656 : ℚ) : ℝ) ≤ ((2578356890813177 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (570 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height017.height_factor_upper_570.trans
      change ((298925430995 / 281474976710656 : ℚ) : ℝ) ≤ ((298925430995 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height017.height_power_upper_570.trans
      change ((161429478704599 / 17592186044416 : ℚ) : ℝ) ≤ ((2582871659273584 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (571 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height017.height_factor_upper_571.trans
      change ((36440402929 / 35184372088832 : ℚ) : ℝ) ≤ ((291523223432 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height017.height_power_upper_571.trans
      change ((2587386379351835 / 281474976710656 : ℚ) : ℝ) ≤ ((2587386379351835 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (572 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height017.height_factor_upper_572.trans
      change ((142152100395 / 140737488355328 : ℚ) : ℝ) ≤ ((284304200790 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height017.height_power_upper_572.trans
      change ((1295950525544011 / 140737488355328 : ℚ) : ℝ) ≤ ((2591901051088022 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (573 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height017.height_factor_upper_573.trans
      change ((277263832647 / 281474976710656 : ℚ) : ℝ) ≤ ((277263832647 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height017.height_power_upper_573.trans
      change ((649103918630547 / 70368744177664 : ℚ) : ℝ) ≤ ((2596415674522188 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (574 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height017.height_factor_upper_574.trans
      change ((135198850273 / 140737488355328 : ℚ) : ℝ) ≤ ((270397700546 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height017.height_power_upper_574.trans
      change ((2600930249694327 / 281474976710656 : ℚ) : ℝ) ≤ ((2600930249694327 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (575 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height017.height_factor_upper_575.trans
      change ((263701495239 / 281474976710656 : ℚ) : ℝ) ≤ ((263701495239 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height017.height_power_upper_575.trans
      change ((2605444776644383 / 281474976710656 : ℚ) : ℝ) ≤ ((2605444776644383 : ℕ) : ℝ) / 2^48
      norm_num
end LegendreK6.M2Pilot.FactorBounds.Height017
