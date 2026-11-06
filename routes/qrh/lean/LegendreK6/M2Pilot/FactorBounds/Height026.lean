import LegendreK6.M2Pilot.Enclosures.Height026
import LegendreK6.M2PilotIntegerData

/-! Join checked analytic enclosures to the exact dyadic witness table. -/
namespace LegendreK6.M2Pilot.FactorBounds.Height026
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem bounds (i : Fin 988) (hlo : 832 ≤ i.val) (hhi : i.val < 864) :
    heightFactor i ≤ heightDyadicFactor i ∧ heightPower i ≤ heightDyadicPower i := by
  interval_cases hi : i.val
  · have heq : i = (832 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height026.height_factor_upper_832.trans
      change ((103493413 / 70368744177664 : ℚ) : ℝ) ≤ ((413973652 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height026.height_power_upper_832.trans
      change ((470523164943641 / 35184372088832 : ℚ) : ℝ) ≤ ((3764185319549128 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (833 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height026.height_factor_upper_833.trans
      change ((201842957 / 140737488355328 : ℚ) : ℝ) ≤ ((403685914 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height026.height_power_upper_833.trans
      change ((1884344305011793 / 140737488355328 : ℚ) : ℝ) ≤ ((3768688610023586 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (834 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height026.height_factor_upper_834.trans
      change ((393653751 / 281474976710656 : ℚ) : ℝ) ≤ ((393653751 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height026.height_power_upper_834.trans
      change ((1886595930580929 / 140737488355328 : ℚ) : ℝ) ≤ ((3773191861161858 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (835 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height026.height_factor_upper_835.trans
      change ((11995963 / 8796093022208 : ℚ) : ℝ) ≤ ((383870816 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height026.height_power_upper_835.trans
      change ((3777695072993337 / 281474976710656 : ℚ) : ℝ) ≤ ((3777695072993337 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (836 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height026.height_factor_upper_836.trans
      change ((187165461 / 140737488355328 : ℚ) : ℝ) ≤ ((374330922 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height026.height_power_upper_836.trans
      change ((3782198245547385 / 281474976710656 : ℚ) : ℝ) ≤ ((3782198245547385 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (837 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height026.height_factor_upper_837.trans
      change ((182514017 / 140737488355328 : ℚ) : ℝ) ≤ ((365028034 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height026.height_power_upper_837.trans
      change ((1893350689426665 / 140737488355328 : ℚ) : ℝ) ≤ ((3786701378853330 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (838 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height026.height_factor_upper_838.trans
      change ((177978133 / 140737488355328 : ℚ) : ℝ) ≤ ((355956266 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height026.height_power_upper_838.trans
      change ((1895602236470233 / 140737488355328 : ℚ) : ℝ) ≤ ((3791204472940466 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (839 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height026.height_factor_upper_839.trans
      change ((43388735 / 35184372088832 : ℚ) : ℝ) ≤ ((347109880 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height026.height_power_upper_839.trans
      change ((3795707527838055 / 281474976710656 : ℚ) : ℝ) ≤ ((3795707527838055 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (840 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height026.height_factor_upper_840.trans
      change ((169241639 / 140737488355328 : ℚ) : ℝ) ≤ ((338483278 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height026.height_power_upper_840.trans
      change ((3800210543575329 / 281474976710656 : ℚ) : ℝ) ≤ ((3800210543575329 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (841 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height026.height_factor_upper_841.trans
      change ((82517751 / 70368744177664 : ℚ) : ℝ) ≤ ((330071004 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height026.height_power_upper_841.trans
      change ((1902356760090741 / 140737488355328 : ℚ) : ℝ) ≤ ((3804713520181482 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (842 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height026.height_factor_upper_842.trans
      change ((321867735 / 281474976710656 : ℚ) : ℝ) ≤ ((321867735 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height026.height_power_upper_842.trans
      change ((238076028605355 / 17592186044416 : ℚ) : ℝ) ≤ ((3809216457685680 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (843 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height026.height_factor_upper_843.trans
      change ((156934141 / 140737488355328 : ℚ) : ℝ) ≤ ((313868282 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height026.height_power_upper_843.trans
      change ((3813719356117055 / 281474976710656 : ℚ) : ℝ) ≤ ((3813719356117055 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (844 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height026.height_factor_upper_844.trans
      change ((153033791 / 140737488355328 : ℚ) : ℝ) ≤ ((306067582 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height026.height_power_upper_844.trans
      change ((59659722117261 / 4398046511104 : ℚ) : ℝ) ≤ ((3818222215504704 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (845 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height026.height_factor_upper_845.trans
      change ((74615175 / 70368744177664 : ℚ) : ℝ) ≤ ((298460700 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height026.height_power_upper_845.trans
      change ((59730078685589 / 4398046511104 : ℚ) : ℝ) ≤ ((3822725035877696 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (846 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height026.height_factor_upper_846.trans
      change ((291042823 / 281474976710656 : ℚ) : ℝ) ≤ ((291042823 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height026.height_power_upper_846.trans
      change ((3827227817265063 / 281474976710656 : ℚ) : ℝ) ≤ ((3827227817265063 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (847 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height026.height_factor_upper_847.trans
      change ((283809257 / 281474976710656 : ℚ) : ℝ) ≤ ((283809257 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height026.height_power_upper_847.trans
      change ((59870789995247 / 4398046511104 : ℚ) : ℝ) ≤ ((3831730559695808 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (848 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height026.height_factor_upper_848.trans
      change ((276755425 / 281474976710656 : ℚ) : ℝ) ≤ ((276755425 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height026.height_power_upper_848.trans
      change ((3836233263198901 / 281474976710656 : ℚ) : ℝ) ≤ ((3836233263198901 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (849 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height026.height_factor_upper_849.trans
      change ((269876863 / 281474976710656 : ℚ) : ℝ) ≤ ((269876863 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height026.height_power_upper_849.trans
      change ((1920367963901639 / 140737488355328 : ℚ) : ℝ) ≤ ((3840735927803278 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (850 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height026.height_factor_upper_850.trans
      change ((263169219 / 281474976710656 : ℚ) : ℝ) ≤ ((263169219 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height026.height_power_upper_850.trans
      change ((961309638384461 / 70368744177664 : ℚ) : ℝ) ≤ ((3845238553537844 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (851 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height026.height_factor_upper_851.trans
      change ((32078531 / 35184372088832 : ℚ) : ℝ) ≤ ((256628248 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height026.height_power_upper_851.trans
      change ((240608821276967 / 17592186044416 : ℚ) : ℝ) ≤ ((3849741140431472 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (852 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height026.height_factor_upper_852.trans
      change ((125124905 / 140737488355328 : ℚ) : ℝ) ≤ ((250249810 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height026.height_power_upper_852.trans
      change ((3854243688513003 / 281474976710656 : ℚ) : ℝ) ≤ ((3854243688513003 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (853 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height026.height_factor_upper_853.trans
      change ((61007467 / 70368744177664 : ℚ) : ℝ) ≤ ((244029868 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height026.height_power_upper_853.trans
      change ((964686549452811 / 70368744177664 : ℚ) : ℝ) ≤ ((3858746197811244 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (854 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height026.height_factor_upper_854.trans
      change ((237964487 / 281474976710656 : ℚ) : ℝ) ≤ ((237964487 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height026.height_power_upper_854.trans
      change ((3863248668354973 / 281474976710656 : ℚ) : ℝ) ≤ ((3863248668354973 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (855 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height026.height_factor_upper_855.trans
      change ((58012457 / 70368744177664 : ℚ) : ℝ) ≤ ((232049828 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height026.height_power_upper_855.trans
      change ((966937775043233 / 70368744177664 : ℚ) : ℝ) ≤ ((3867751100172932 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (856 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height026.height_factor_upper_856.trans
      change ((113141073 / 140737488355328 : ℚ) : ℝ) ≤ ((226282146 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height026.height_power_upper_856.trans
      change ((968063373323459 / 70368744177664 : ℚ) : ℝ) ≤ ((3872253493293836 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (857 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height026.height_factor_upper_857.trans
      change ((220657793 / 281474976710656 : ℚ) : ℝ) ≤ ((220657793 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height026.height_power_upper_857.trans
      change ((969188961936591 / 70368744177664 : ℚ) : ℝ) ≤ ((3876755847746364 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (858 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height026.height_factor_upper_858.trans
      change ((215173207 / 281474976710656 : ℚ) : ℝ) ≤ ((215173207 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height026.height_power_upper_858.trans
      change ((970314540889791 / 70368744177664 : ℚ) : ℝ) ≤ ((3881258163559164 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (859 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height026.height_factor_upper_859.trans
      change ((209824917 / 281474976710656 : ℚ) : ℝ) ≤ ((209824917 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height026.height_power_upper_859.trans
      change ((1942880220380427 / 140737488355328 : ℚ) : ℝ) ≤ ((3885760440760854 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (860 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height026.height_factor_upper_860.trans
      change ((204609537 / 281474976710656 : ℚ) : ℝ) ≤ ((204609537 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height026.height_power_upper_860.trans
      change ((1945131339690009 / 140737488355328 : ℚ) : ℝ) ≤ ((3890262679380018 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (861 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height026.height_factor_upper_861.trans
      change ((24940471 / 35184372088832 : ℚ) : ℝ) ≤ ((199523768 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height026.height_power_upper_861.trans
      change ((1947382439722605 / 140737488355328 : ℚ) : ℝ) ≤ ((3894764879445210 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (862 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height026.height_factor_upper_862.trans
      change ((48641097 / 70368744177664 : ℚ) : ℝ) ≤ ((194564388 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height026.height_power_upper_862.trans
      change ((3899267040984951 / 281474976710656 : ℚ) : ℝ) ≤ ((3899267040984951 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (863 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height026.height_factor_upper_863.trans
      change ((189728259 / 281474976710656 : ℚ) : ℝ) ≤ ((189728259 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height026.height_power_upper_863.trans
      change ((3903769164027731 / 281474976710656 : ℚ) : ℝ) ≤ ((3903769164027731 : ℕ) : ℝ) / 2^48
      norm_num
end LegendreK6.M2Pilot.FactorBounds.Height026
