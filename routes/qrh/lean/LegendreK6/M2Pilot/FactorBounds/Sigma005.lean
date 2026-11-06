import LegendreK6.M2Pilot.Enclosures.Sigma005
import LegendreK6.M2PilotIntegerData

/-! Join checked analytic enclosures to the exact dyadic witness table. -/
namespace LegendreK6.M2Pilot.FactorBounds.Sigma005
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem bounds (i : Fin 1536) (hlo : 640 ≤ i.val) (hhi : i.val < 768) :
    sigmaFactor i ≤ sigmaDyadicFactor i ∧ sigmaPower i ≤ sigmaDyadicPower i := by
  interval_cases hi : i.val
  · have heq : i = (640 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_640.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_640.trans
      change ((30547671891079 / 70368744177664 : ℚ) : ℝ) ≤ ((122190687564316 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (641 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_641.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_641.trans
      change ((122076493624587 / 281474976710656 : ℚ) : ℝ) ≤ ((122076493624587 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (642 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_642.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_642.trans
      change ((121962258174883 / 281474976710656 : ℚ) : ℝ) ≤ ((121962258174883 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (643 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_643.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_643.trans
      change ((121847981192567 / 281474976710656 : ℚ) : ℝ) ≤ ((121847981192567 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (644 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_644.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_644.trans
      change ((121733662654985 / 281474976710656 : ℚ) : ℝ) ≤ ((121733662654985 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (645 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_645.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_645.trans
      change ((60809651269733 / 140737488355328 : ℚ) : ℝ) ≤ ((121619302539466 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (646 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_646.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_646.trans
      change ((60752450411661 / 140737488355328 : ℚ) : ℝ) ≤ ((121504900823322 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (647 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_647.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_647.trans
      change ((121390457483851 / 281474976710656 : ℚ) : ℝ) ≤ ((121390457483851 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (648 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_648.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_648.trans
      change ((121275972498333 / 281474976710656 : ℚ) : ℝ) ≤ ((121275972498333 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (649 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_649.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_649.trans
      change ((121161445844029 / 281474976710656 : ℚ) : ℝ) ≤ ((121161445844029 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (650 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_650.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_650.trans
      change ((30261719374547 / 70368744177664 : ℚ) : ℝ) ≤ ((121046877498188 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (651 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_651.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_651.trans
      change ((120932267438039 / 281474976710656 : ℚ) : ℝ) ≤ ((120932267438039 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (652 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_652.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_652.trans
      change ((120817615640797 / 281474976710656 : ℚ) : ℝ) ≤ ((120817615640797 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (653 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_653.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_653.trans
      change ((120702922083657 / 281474976710656 : ℚ) : ℝ) ≤ ((120702922083657 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (654 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_654.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_654.trans
      change ((120588186743801 / 281474976710656 : ℚ) : ℝ) ≤ ((120588186743801 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (655 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_655.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_655.trans
      change ((120473409598391 / 281474976710656 : ℚ) : ℝ) ≤ ((120473409598391 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (656 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_656.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_656.trans
      change ((1880602978509 / 4398046511104 : ℚ) : ℝ) ≤ ((120358590624576 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (657 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_657.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_657.trans
      change ((60121864899743 / 140737488355328 : ℚ) : ℝ) ≤ ((120243729799486 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (658 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_658.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_658.trans
      change ((60064413550117 / 140737488355328 : ℚ) : ℝ) ≤ ((120128827100234 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (659 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_659.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_659.trans
      change ((60006941251959 / 140737488355328 : ℚ) : ℝ) ≤ ((120013882503918 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (660 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_660.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_660.trans
      change ((59949447993809 / 140737488355328 : ℚ) : ℝ) ≤ ((119898895987618 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (661 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_661.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_661.trans
      change ((119783867528397 / 281474976710656 : ℚ) : ℝ) ≤ ((119783867528397 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (662 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_662.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_662.trans
      change ((119668797103303 / 281474976710656 : ℚ) : ℝ) ≤ ((119668797103303 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (663 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_663.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_663.trans
      change ((119553684689365 / 281474976710656 : ℚ) : ℝ) ≤ ((119553684689365 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (664 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_664.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_664.trans
      change ((59719265131799 / 140737488355328 : ℚ) : ℝ) ≤ ((119438530263598 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (665 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_665.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_665.trans
      change ((119323333802997 / 281474976710656 : ℚ) : ℝ) ≤ ((119323333802997 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (666 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_666.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_666.trans
      change ((119208095284543 / 281474976710656 : ℚ) : ℝ) ≤ ((119208095284543 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (667 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_667.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_667.trans
      change ((59546407342599 / 140737488355328 : ℚ) : ℝ) ≤ ((119092814685198 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (668 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_668.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_668.trans
      change ((118977491981909 / 281474976710656 : ℚ) : ℝ) ≤ ((118977491981909 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (669 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_669.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_669.trans
      change ((118862127151605 / 281474976710656 : ℚ) : ℝ) ≤ ((118862127151605 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (670 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_670.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_670.trans
      change ((118746720171199 / 281474976710656 : ℚ) : ℝ) ≤ ((118746720171199 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (671 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_671.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_671.trans
      change ((59315635508793 / 140737488355328 : ℚ) : ℝ) ≤ ((118631271017586 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (672 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_672.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_672.trans
      change ((118515779667645 / 281474976710656 : ℚ) : ℝ) ≤ ((118515779667645 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (673 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_673.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_673.trans
      change ((59200123049119 / 140737488355328 : ℚ) : ℝ) ≤ ((118400246098238 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (674 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_674.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_674.trans
      change ((118284670286209 / 281474976710656 : ℚ) : ℝ) ≤ ((118284670286209 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (675 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_675.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_675.trans
      change ((118169052208387 / 281474976710656 : ℚ) : ℝ) ≤ ((118169052208387 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (676 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_676.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_676.trans
      change ((118053391841583 / 281474976710656 : ℚ) : ℝ) ≤ ((118053391841583 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (677 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_677.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_677.trans
      change ((58968844581295 / 140737488355328 : ℚ) : ℝ) ≤ ((117937689162590 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (678 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_678.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_678.trans
      change ((58910972074093 / 140737488355328 : ℚ) : ℝ) ≤ ((117821944148186 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (679 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_679.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_679.trans
      change ((117706156775131 / 281474976710656 : ℚ) : ℝ) ≤ ((117706156775131 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (680 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_680.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_680.trans
      change ((117590327020167 / 281474976710656 : ℚ) : ℝ) ≤ ((117590327020167 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (681 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_681.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_681.trans
      change ((58737227430011 / 140737488355328 : ℚ) : ℝ) ≤ ((117474454860022 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (682 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_682.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_682.trans
      change ((117358540271403 / 281474976710656 : ℚ) : ℝ) ≤ ((117358540271403 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (683 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_683.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_683.trans
      change ((117242583231003 / 281474976710656 : ℚ) : ℝ) ≤ ((117242583231003 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (684 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_684.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_684.trans
      change ((117126583715497 / 281474976710656 : ℚ) : ℝ) ≤ ((117126583715497 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (685 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_685.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_685.trans
      change ((58505270850771 / 140737488355328 : ℚ) : ℝ) ≤ ((117010541701542 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (686 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_686.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_686.trans
      change ((116894457165779 / 281474976710656 : ℚ) : ℝ) ≤ ((116894457165779 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (687 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_687.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_687.trans
      change ((3649322815151 / 8796093022208 : ℚ) : ℝ) ≤ ((116778330084832 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (688 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_688.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_688.trans
      change ((116662160435307 / 281474976710656 : ℚ) : ℝ) ≤ ((116662160435307 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (689 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_689.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_689.trans
      change ((113814402533 / 274877906944 : ℚ) : ℝ) ≤ ((116545948193792 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (690 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_690.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_690.trans
      change ((58214846668431 / 140737488355328 : ℚ) : ℝ) ≤ ((116429693336862 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (691 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_691.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_691.trans
      change ((116313395841069 / 281474976710656 : ℚ) : ℝ) ≤ ((116313395841069 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (692 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_692.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_692.trans
      change ((14524631960369 / 35184372088832 : ℚ) : ℝ) ≤ ((116197055682952 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (693 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_693.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_693.trans
      change ((116080672839031 / 281474976710656 : ℚ) : ℝ) ≤ ((116080672839031 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (694 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_694.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_694.trans
      change ((57982123642905 / 140737488355328 : ℚ) : ℝ) ≤ ((115964247285810 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (695 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_695.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_695.trans
      change ((57923889499887 / 140737488355328 : ℚ) : ℝ) ≤ ((115847778999774 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (696 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_696.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_696.trans
      change ((7233204247337 / 17592186044416 : ℚ) : ℝ) ≤ ((115731267957392 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (697 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_697.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_697.trans
      change ((28903678533779 / 70368744177664 : ℚ) : ℝ) ≤ ((115614714135116 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (698 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_698.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_698.trans
      change ((28874529377345 / 70368744177664 : ℚ) : ℝ) ≤ ((115498117509380 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (699 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_699.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_699.trans
      change ((14422684757075 / 35184372088832 : ℚ) : ℝ) ≤ ((115381478056600 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (700 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_700.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_700.trans
      change ((14408099469147 / 35184372088832 : ℚ) : ℝ) ≤ ((115264795753176 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (701 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_701.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_701.trans
      change ((115148070575491 / 281474976710656 : ℚ) : ℝ) ≤ ((115148070575491 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (702 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_702.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_702.trans
      change ((28757825624977 / 70368744177664 : ℚ) : ℝ) ≤ ((115031302499908 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (703 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_703.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_703.trans
      change ((14364311437847 / 35184372088832 : ℚ) : ℝ) ≤ ((114914491502776 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (704 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_704.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_704.trans
      change ((114797637560425 / 281474976710656 : ℚ) : ℝ) ≤ ((114797637560425 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (705 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_705.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_705.trans
      change ((57340370324583 / 140737488355328 : ℚ) : ℝ) ≤ ((114680740649166 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (706 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_706.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_706.trans
      change ((7160237546581 / 17592186044416 : ℚ) : ℝ) ≤ ((114563800745296 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (707 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_707.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_707.trans
      change ((28611704456273 / 70368744177664 : ℚ) : ℝ) ≤ ((114446817825092 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (708 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_708.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_708.trans
      change ((57164895932407 / 140737488355328 : ℚ) : ℝ) ≤ ((114329791864814 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (709 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_709.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_709.trans
      change ((57106361420353 / 140737488355328 : ℚ) : ℝ) ≤ ((114212722840706 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (710 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_710.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_710.trans
      change ((3565487835281 / 8796093022208 : ℚ) : ℝ) ≤ ((114095610728992 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (711 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_711.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_711.trans
      change ((14247306938235 / 35184372088832 : ℚ) : ℝ) ≤ ((113978455505880 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (712 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_712.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_712.trans
      change ((113861257147561 / 281474976710656 : ℚ) : ℝ) ≤ ((113861257147561 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (713 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_713.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_713.trans
      change ((113744015630207 / 281474976710656 : ℚ) : ℝ) ≤ ((113744015630207 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (714 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_714.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_714.trans
      change ((56813365464987 / 140737488355328 : ℚ) : ℝ) ≤ ((113626730929974 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (715 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_715.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_715.trans
      change ((14188675377875 / 35184372088832 : ℚ) : ℝ) ≤ ((113509403023000 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (716 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_716.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_716.trans
      change ((28348007971351 / 70368744177664 : ℚ) : ℝ) ≤ ((113392031885404 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (717 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_717.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_717.trans
      change ((14159327186661 / 35184372088832 : ℚ) : ℝ) ≤ ((113274617493288 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (718 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_718.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_718.trans
      change ((113157159822739 / 281474976710656 : ℚ) : ℝ) ≤ ((113157159822739 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (719 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_719.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_719.trans
      change ((56519829424911 / 140737488355328 : ℚ) : ℝ) ≤ ((113039658849822 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (720 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_720.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_720.trans
      change ((28230528637647 / 70368744177664 : ℚ) : ℝ) ≤ ((112922114550588 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (721 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_721.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_721.trans
      change ((112804526901069 / 281474976710656 : ℚ) : ℝ) ≤ ((112804526901069 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (722 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_722.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_722.trans
      change ((56343447938639 / 140737488355328 : ℚ) : ℝ) ≤ ((112686895877278 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (723 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_723.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_723.trans
      change ((28142305363803 / 70368744177664 : ℚ) : ℝ) ≤ ((112569221455212 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (724 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_724.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_724.trans
      change ((112451503610851 / 281474976710656 : ℚ) : ℝ) ≤ ((112451503610851 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (725 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_725.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_725.trans
      change ((56166871160077 / 140737488355328 : ℚ) : ℝ) ≤ ((112333742320154 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (726 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_726.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_726.trans
      change ((56107968779533 / 140737488355328 : ℚ) : ℝ) ≤ ((112215937559066 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (727 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_727.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_727.trans
      change ((14012261162939 / 35184372088832 : ℚ) : ℝ) ≤ ((112098089303512 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (728 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_728.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_728.trans
      change ((13997524691175 / 35184372088832 : ℚ) : ℝ) ≤ ((111980197529400 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (729 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_729.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_729.trans
      change ((111862262212619 / 281474976710656 : ℚ) : ℝ) ≤ ((111862262212619 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (730 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_730.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_730.trans
      change ((111744283329043 / 281474976710656 : ℚ) : ℝ) ≤ ((111744283329043 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (731 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_731.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_731.trans
      change ((111626260854525 / 281474976710656 : ℚ) : ℝ) ≤ ((111626260854525 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (732 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_732.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_732.trans
      change ((55754097382451 / 140737488355328 : ℚ) : ℝ) ≤ ((111508194764902 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (733 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_733.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_733.trans
      change ((13923760629499 / 35184372088832 : ℚ) : ℝ) ≤ ((111390085035992 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (734 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_734.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_734.trans
      change ((111271931643597 / 281474976710656 : ℚ) : ℝ) ≤ ((111271931643597 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (735 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_735.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_735.trans
      change ((111153734563499 / 281474976710656 : ℚ) : ℝ) ≤ ((111153734563499 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (736 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_736.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_736.trans
      change ((55517746885731 / 140737488355328 : ℚ) : ℝ) ≤ ((111035493771462 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (737 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_737.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_737.trans
      change ((110917209243235 / 281474976710656 : ℚ) : ℝ) ≤ ((110917209243235 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (738 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_738.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_738.trans
      change ((110798880954547 / 281474976710656 : ℚ) : ℝ) ≤ ((110798880954547 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (739 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_739.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_739.trans
      change ((110680508881107 / 281474976710656 : ℚ) : ℝ) ≤ ((110680508881107 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (740 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_740.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_740.trans
      change ((55281046499305 / 140737488355328 : ℚ) : ℝ) ≤ ((110562092998610 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (741 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_741.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_741.trans
      change ((110443633282731 / 281474976710656 : ℚ) : ℝ) ≤ ((110443633282731 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (742 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_742.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_742.trans
      change ((55162564854563 / 140737488355328 : ℚ) : ℝ) ≤ ((110325129709126 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (743 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_743.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_743.trans
      change ((110206582253435 / 281474976710656 : ℚ) : ℝ) ≤ ((110206582253435 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (744 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_744.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_744.trans
      change ((110087990891279 / 281474976710656 : ℚ) : ℝ) ≤ ((110087990891279 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (745 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_745.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_745.trans
      change ((109969355598261 / 281474976710656 : ℚ) : ℝ) ≤ ((109969355598261 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (746 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_746.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_746.trans
      change ((54925338174983 / 140737488355328 : ℚ) : ℝ) ≤ ((109850676349966 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (747 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_747.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_747.trans
      change ((109731953121961 / 281474976710656 : ℚ) : ℝ) ≤ ((109731953121961 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (748 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_748.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_748.trans
      change ((54806592944897 / 140737488355328 : ℚ) : ℝ) ≤ ((109613185889794 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (749 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_749.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_749.trans
      change ((27373593657249 / 70368744177664 : ℚ) : ℝ) ≤ ((109494374628996 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (750 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_750.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_750.trans
      change ((109375519315079 / 281474976710656 : ℚ) : ℝ) ≤ ((109375519315079 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (751 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_751.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_751.trans
      change ((54628309961769 / 140737488355328 : ℚ) : ℝ) ≤ ((109256619923538 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (752 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_752.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_752.trans
      change ((109137676429849 / 281474976710656 : ℚ) : ℝ) ≤ ((109137676429849 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (753 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_753.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_753.trans
      change ((54509344404735 / 140737488355328 : ℚ) : ℝ) ≤ ((109018688809470 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (754 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_754.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_754.trans
      change ((6806228564865 / 17592186044416 : ℚ) : ℝ) ≤ ((108899657037840 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (755 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_755.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_755.trans
      change ((108780581090381 / 281474976710656 : ℚ) : ℝ) ≤ ((108780581090381 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (756 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_756.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_756.trans
      change ((3395670654453 / 8796093022208 : ℚ) : ℝ) ≤ ((108661460942496 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (757 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_757.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_757.trans
      change ((54271148284785 / 140737488355328 : ℚ) : ℝ) ≤ ((108542296569570 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (758 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_758.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_758.trans
      change ((108423087946969 / 281474976710656 : ℚ) : ℝ) ≤ ((108423087946969 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (759 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_759.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_759.trans
      change ((108303835050043 / 281474976710656 : ℚ) : ℝ) ≤ ((108303835050043 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (760 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_760.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_760.trans
      change ((108184537854121 / 281474976710656 : ℚ) : ℝ) ≤ ((108184537854121 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (761 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_761.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_761.trans
      change ((108065196334515 / 281474976710656 : ℚ) : ℝ) ≤ ((108065196334515 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (762 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_762.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_762.trans
      change ((107945810466517 / 281474976710656 : ℚ) : ℝ) ≤ ((107945810466517 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (763 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_763.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_763.trans
      change ((26956595056351 / 70368744177664 : ℚ) : ℝ) ≤ ((107826380225404 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (764 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_764.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_764.trans
      change ((420730099947 / 1099511627776 : ℚ) : ℝ) ≤ ((107706905586432 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (765 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_765.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_765.trans
      change ((107587386524839 / 281474976710656 : ℚ) : ℝ) ≤ ((107587386524839 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (766 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_766.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_766.trans
      change ((107467823015845 / 281474976710656 : ℚ) : ℝ) ≤ ((107467823015845 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (767 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_767.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_767.trans
      change ((26837053758663 / 70368744177664 : ℚ) : ℝ) ≤ ((107348215034652 : ℕ) : ℝ) / 2^48
      norm_num
end LegendreK6.M2Pilot.FactorBounds.Sigma005
