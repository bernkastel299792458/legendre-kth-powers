import LegendreK6.M2Pilot.Enclosures.Height010
import LegendreK6.M2PilotIntegerData

/-! Join checked analytic enclosures to the exact dyadic witness table. -/
namespace LegendreK6.M2Pilot.FactorBounds.Height010
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem bounds (i : Fin 988) (hlo : 320 ≤ i.val) (hhi : i.val < 352) :
    heightFactor i ≤ heightDyadicFactor i ∧ heightPower i ≤ heightDyadicPower i := by
  interval_cases hi : i.val
  · have heq : i = (320 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height010.height_factor_upper_320.trans
      change ((155638500030621 / 281474976710656 : ℚ) : ℝ) ≤ ((155638500030621 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height010.height_power_upper_320.trans
      change ((1452560319069065 / 281474976710656 : ℚ) : ℝ) ≤ ((1452560319069065 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (321 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height010.height_factor_upper_321.trans
      change ((151801438633065 / 281474976710656 : ℚ) : ℝ) ≤ ((151801438633065 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height010.height_power_upper_321.trans
      change ((728544263710715 / 140737488355328 : ℚ) : ℝ) ≤ ((1457088527421430 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (322 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height010.height_factor_upper_322.trans
      change ((37014725267231 / 70368744177664 : ℚ) : ℝ) ≤ ((148058901068924 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height010.height_power_upper_322.trans
      change ((730808337805583 / 140737488355328 : ℚ) : ℝ) ≤ ((1461616675611166 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (323 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height010.height_factor_upper_323.trans
      change ((72204280342825 / 140737488355328 : ℚ) : ℝ) ≤ ((144408560685650 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height010.height_power_upper_323.trans
      change ((1466144763693865 / 281474976710656 : ℚ) : ℝ) ≤ ((1466144763693865 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (324 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height010.height_factor_upper_324.trans
      change ((70424074025841 / 140737488355328 : ℚ) : ℝ) ≤ ((140848148051682 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height010.height_power_upper_324.trans
      change ((91917049482815 / 17592186044416 : ℚ) : ℝ) ≤ ((1470672791725040 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (325 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height010.height_factor_upper_325.trans
      change ((2146491399225 / 4398046511104 : ℚ) : ℝ) ≤ ((137375449550400 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height010.height_power_upper_325.trans
      change ((737600379880063 / 140737488355328 : ℚ) : ℝ) ≤ ((1475200759760126 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (326 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height010.height_factor_upper_326.trans
      change ((133988306008607 / 281474976710656 : ℚ) : ℝ) ≤ ((133988306008607 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height010.height_power_upper_326.trans
      change ((1479728667854485 / 281474976710656 : ℚ) : ℝ) ≤ ((1479728667854485 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (327 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height010.height_factor_upper_327.trans
      change ((65342305679337 / 140737488355328 : ℚ) : ℝ) ≤ ((130684611358674 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height010.height_power_upper_327.trans
      change ((742128258031699 / 140737488355328 : ℚ) : ℝ) ≤ ((1484256516063398 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (328 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height010.height_factor_upper_328.trans
      change ((127462311333537 / 281474976710656 : ℚ) : ℝ) ≤ ((127462311333537 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height010.height_power_upper_328.trans
      change ((186098038055259 / 35184372088832 : ℚ) : ℝ) ≤ ((1488784304442072 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (329 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height010.height_factor_upper_329.trans
      change ((1942490659277 / 4398046511104 : ℚ) : ℝ) ≤ ((124319402193728 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height010.height_power_upper_329.trans
      change ((746656016522819 / 140737488355328 : ℚ) : ℝ) ≤ ((1493312033045638 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (330 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height010.height_factor_upper_330.trans
      change ((30313482371417 / 70368744177664 : ℚ) : ℝ) ≤ ((121253929485668 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height010.height_power_upper_330.trans
      change ((1497839701929151 / 281474976710656 : ℚ) : ℝ) ≤ ((1497839701929151 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (331 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height010.height_factor_upper_331.trans
      change ((3695749588451 / 8796093022208 : ℚ) : ℝ) ≤ ((118263986830432 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height010.height_power_upper_331.trans
      change ((375591827786897 / 70368744177664 : ℚ) : ℝ) ≤ ((1502367311147588 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (332 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height010.height_factor_upper_332.trans
      change ((28836928685569 / 70368744177664 : ℚ) : ℝ) ≤ ((115347714742276 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height010.height_power_upper_332.trans
      change ((1506894860755851 / 281474976710656 : ℚ) : ℝ) ≤ ((1506894860755851 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (333 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height010.height_factor_upper_333.trans
      change ((56251649738075 / 140737488355328 : ℚ) : ℝ) ≤ ((112503299476150 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height010.height_power_upper_333.trans
      change ((23615974231387 / 4398046511104 : ℚ) : ℝ) ≤ ((1511422350808768 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (334 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height010.height_factor_upper_334.trans
      change ((109728971903527 / 281474976710656 : ℚ) : ℝ) ≤ ((109728971903527 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height010.height_power_upper_334.trans
      change ((23686715333767 / 4398046511104 : ℚ) : ℝ) ≤ ((1515949781361088 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (335 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height010.height_factor_upper_335.trans
      change ((53511503207913 / 140737488355328 : ℚ) : ℝ) ≤ ((107023006415826 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height010.height_power_upper_335.trans
      change ((47514911014609 / 8796093022208 : ℚ) : ℝ) ≤ ((1520477152467488 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (336 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height010.height_factor_upper_336.trans
      change ((104383719854771 / 281474976710656 : ℚ) : ℝ) ≤ ((104383719854771 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height010.height_power_upper_336.trans
      change ((190625558022821 / 35184372088832 : ℚ) : ℝ) ≤ ((1525004464182568 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (337 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height010.height_factor_upper_337.trans
      change ((50904735234501 / 140737488355328 : ℚ) : ℝ) ≤ ((101809470469002 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height010.height_power_upper_337.trans
      change ((1529531716560853 / 281474976710656 : ℚ) : ℝ) ≤ ((1529531716560853 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (338 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height010.height_factor_upper_338.trans
      change ((99298656896327 / 281474976710656 : ℚ) : ℝ) ≤ ((99298656896327 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height010.height_power_upper_338.trans
      change ((191757363707099 / 35184372088832 : ℚ) : ℝ) ≤ ((1534058909656792 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (339 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height010.height_factor_upper_339.trans
      change ((96849717170947 / 281474976710656 : ℚ) : ℝ) ≤ ((96849717170947 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height010.height_power_upper_339.trans
      change ((1538586043524761 / 281474976710656 : ℚ) : ℝ) ≤ ((1538586043524761 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (340 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height010.height_factor_upper_340.trans
      change ((11807640969385 / 35184372088832 : ℚ) : ℝ) ≤ ((94461127755080 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height010.height_power_upper_340.trans
      change ((385778279554765 / 70368744177664 : ℚ) : ℝ) ≤ ((1543113118219060 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (341 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height010.height_factor_upper_341.trans
      change ((92131402594353 / 281474976710656 : ℚ) : ℝ) ≤ ((92131402594353 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height010.height_power_upper_341.trans
      change ((773820066896957 / 140737488355328 : ℚ) : ℝ) ≤ ((1547640133793914 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (342 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height010.height_factor_upper_342.trans
      change ((5616193262275 / 17592186044416 : ℚ) : ℝ) ≤ ((89859092196400 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height010.height_power_upper_342.trans
      change ((1552167090303475 / 281474976710656 : ℚ) : ℝ) ≤ ((1552167090303475 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (343 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height010.height_factor_upper_343.trans
      change ((43821391366043 / 140737488355328 : ℚ) : ℝ) ≤ ((87642782732086 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height010.height_power_upper_343.trans
      change ((1556693987801819 / 281474976710656 : ℚ) : ℝ) ≤ ((1556693987801819 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (344 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height010.height_factor_upper_344.trans
      change ((42740547579403 / 140737488355328 : ℚ) : ℝ) ≤ ((85481095158806 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height010.height_power_upper_344.trans
      change ((1561220826342949 / 281474976710656 : ℚ) : ℝ) ≤ ((1561220826342949 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (345 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height010.height_factor_upper_345.trans
      change ((83372684365319 / 281474976710656 : ℚ) : ℝ) ≤ ((83372684365319 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height010.height_power_upper_345.trans
      change ((1565747605980793 / 281474976710656 : ℚ) : ℝ) ≤ ((1565747605980793 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (346 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height010.height_factor_upper_346.trans
      change ((20329059584395 / 70368744177664 : ℚ) : ℝ) ≤ ((81316238337580 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height010.height_power_upper_346.trans
      change ((785137163384603 / 140737488355328 : ℚ) : ℝ) ≤ ((1570274326769206 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (347 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height010.height_factor_upper_347.trans
      change ((79310477345065 / 281474976710656 : ℚ) : ℝ) ≤ ((79310477345065 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height010.height_power_upper_347.trans
      change ((98425061797623 / 17592186044416 : ℚ) : ℝ) ≤ ((1574800988761968 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (348 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height010.height_factor_upper_348.trans
      change ((38677076573543 / 140737488355328 : ℚ) : ℝ) ≤ ((77354153147086 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height010.height_power_upper_348.trans
      change ((789663796006393 / 140737488355328 : ℚ) : ℝ) ≤ ((1579327592012786 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (349 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height010.height_factor_upper_349.trans
      change ((75446048218589 / 281474976710656 : ℚ) : ℝ) ≤ ((75446048218589 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height010.height_power_upper_349.trans
      change ((1583854136575293 / 281474976710656 : ℚ) : ℝ) ≤ ((1583854136575293 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (350 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height010.height_factor_upper_350.trans
      change ((36792487497491 / 140737488355328 : ℚ) : ℝ) ≤ ((73584974994982 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height010.height_power_upper_350.trans
      change ((794190311251525 / 140737488355328 : ℚ) : ℝ) ≤ ((1588380622503050 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (351 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height010.height_factor_upper_351.trans
      change ((71769775135505 / 281474976710656 : ℚ) : ℝ) ≤ ((71769775135505 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height010.height_power_upper_351.trans
      change ((1592907049849543 / 281474976710656 : ℚ) : ℝ) ≤ ((1592907049849543 : ℕ) : ℝ) / 2^48
      norm_num
end LegendreK6.M2Pilot.FactorBounds.Height010
