import LegendreK6.M2Pilot.Enclosures.Height027
import LegendreK6.M2PilotIntegerData

/-! Join checked analytic enclosures to the exact dyadic witness table. -/
namespace LegendreK6.M2Pilot.FactorBounds.Height027
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem bounds (i : Fin 988) (hlo : 864 ≤ i.val) (hhi : i.val < 896) :
    heightFactor i ≤ heightDyadicFactor i ∧ heightPower i ≤ heightDyadicPower i := by
  interval_cases hi : i.val
  · have heq : i = (864 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height027.height_factor_upper_864.trans
      change ((5781635 / 8796093022208 : ℚ) : ℝ) ≤ ((185012320 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height027.height_power_upper_864.trans
      change ((488533906075251 / 35184372088832 : ℚ) : ℝ) ≤ ((3908271248602008 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (865 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height027.height_factor_upper_865.trans
      change ((11275849 / 17592186044416 : ℚ) : ℝ) ≤ ((180413584 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height027.height_power_upper_865.trans
      change ((3912773294736209 / 281474976710656 : ℚ) : ℝ) ≤ ((3912773294736209 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (866 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height027.height_factor_upper_866.trans
      change ((175929141 / 281474976710656 : ℚ) : ℝ) ≤ ((175929141 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height027.height_power_upper_866.trans
      change ((1958637651229365 / 140737488355328 : ℚ) : ℝ) ≤ ((3917275302458730 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (867 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height027.height_factor_upper_867.trans
      change ((171556151 / 281474976710656 : ℚ) : ℝ) ≤ ((171556151 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height027.height_power_upper_867.trans
      change ((1960888635898967 / 140737488355328 : ℚ) : ℝ) ≤ ((3921777271797934 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (868 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height027.height_factor_upper_868.trans
      change ((167291845 / 281474976710656 : ℚ) : ℝ) ≤ ((167291845 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height027.height_power_upper_868.trans
      change ((3926279202782153 / 281474976710656 : ℚ) : ℝ) ≤ ((3926279202782153 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (869 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height027.height_factor_upper_869.trans
      change ((163133525 / 281474976710656 : ℚ) : ℝ) ≤ ((163133525 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height027.height_power_upper_869.trans
      change ((3930781095439689 / 281474976710656 : ℚ) : ℝ) ≤ ((3930781095439689 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (870 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height027.height_factor_upper_870.trans
      change ((159078557 / 281474976710656 : ℚ) : ℝ) ≤ ((159078557 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height027.height_power_upper_870.trans
      change ((3935282949798811 / 281474976710656 : ℚ) : ℝ) ≤ ((3935282949798811 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (871 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height027.height_factor_upper_871.trans
      change ((155124373 / 281474976710656 : ℚ) : ℝ) ≤ ((155124373 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height027.height_power_upper_871.trans
      change ((3939784765887757 / 281474976710656 : ℚ) : ℝ) ≤ ((3939784765887757 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (872 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height027.height_factor_upper_872.trans
      change ((75634235 / 140737488355328 : ℚ) : ℝ) ≤ ((151268470 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height027.height_power_upper_872.trans
      change ((246517908983421 / 17592186044416 : ℚ) : ℝ) ≤ ((3944286543734736 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (873 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height027.height_factor_upper_873.trans
      change ((147508407 / 281474976710656 : ℚ) : ℝ) ≤ ((147508407 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height027.height_power_upper_873.trans
      change ((3948788283367923 / 281474976710656 : ℚ) : ℝ) ≤ ((3948788283367923 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (874 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height027.height_factor_upper_874.trans
      change ((71920901 / 140737488355328 : ℚ) : ℝ) ≤ ((143841802 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height027.height_power_upper_874.trans
      change ((3953289984815463 / 281474976710656 : ℚ) : ℝ) ≤ ((3953289984815463 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (875 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height027.height_factor_upper_875.trans
      change ((70133167 / 140737488355328 : ℚ) : ℝ) ≤ ((140266334 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height027.height_power_upper_875.trans
      change ((1978895824052735 / 140737488355328 : ℚ) : ℝ) ≤ ((3957791648105470 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (876 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height027.height_factor_upper_876.trans
      change ((68389869 / 140737488355328 : ℚ) : ℝ) ≤ ((136779738 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height027.height_power_upper_876.trans
      change ((1981146636633013 / 140737488355328 : ℚ) : ℝ) ≤ ((3962293273266026 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (877 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height027.height_factor_upper_877.trans
      change ((133379807 / 281474976710656 : ℚ) : ℝ) ≤ ((133379807 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height027.height_power_upper_877.trans
      change ((61981169692581 / 4398046511104 : ℚ) : ℝ) ≤ ((3966794860325184 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (878 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height027.height_factor_upper_878.trans
      change ((130064387 / 281474976710656 : ℚ) : ℝ) ≤ ((130064387 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height027.height_power_upper_878.trans
      change ((992824102327741 / 70368744177664 : ℚ) : ℝ) ≤ ((3971296409310964 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (879 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height027.height_factor_upper_879.trans
      change ((31707845 / 70368744177664 : ℚ) : ℝ) ≤ ((126831380 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height027.height_power_upper_879.trans
      change ((3975797920251357 / 281474976710656 : ℚ) : ℝ) ≤ ((3975797920251357 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (880 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height027.height_factor_upper_880.trans
      change ((7729921 / 17592186044416 : ℚ) : ℝ) ≤ ((123678736 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height027.height_power_upper_880.trans
      change ((3980299393174321 / 281474976710656 : ℚ) : ℝ) ≤ ((3980299393174321 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (881 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height027.height_factor_upper_881.trans
      change ((120604461 / 281474976710656 : ℚ) : ℝ) ≤ ((120604461 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height027.height_power_upper_881.trans
      change ((3984800828107785 / 281474976710656 : ℚ) : ℝ) ≤ ((3984800828107785 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (882 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height027.height_factor_upper_882.trans
      change ((58803303 / 140737488355328 : ℚ) : ℝ) ≤ ((117606606 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height027.height_power_upper_882.trans
      change ((3989302225079647 / 281474976710656 : ℚ) : ℝ) ≤ ((3989302225079647 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (883 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height027.height_factor_upper_883.trans
      change ((14335409 / 35184372088832 : ℚ) : ℝ) ≤ ((114683272 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height027.height_power_upper_883.trans
      change ((3993803584117773 / 281474976710656 : ℚ) : ℝ) ≤ ((3993803584117773 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (884 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height027.height_factor_upper_884.trans
      change ((55916305 / 140737488355328 : ℚ) : ℝ) ≤ ((111832610 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height027.height_power_upper_884.trans
      change ((3998304905249999 / 281474976710656 : ℚ) : ℝ) ≤ ((3998304905249999 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (885 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height027.height_factor_upper_885.trans
      change ((27263203 / 70368744177664 : ℚ) : ℝ) ≤ ((109052812 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height027.height_power_upper_885.trans
      change ((4002806188504131 / 281474976710656 : ℚ) : ℝ) ≤ ((4002806188504131 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (886 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height027.height_factor_upper_886.trans
      change ((106342117 / 281474976710656 : ℚ) : ℝ) ≤ ((106342117 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height027.height_power_upper_886.trans
      change ((500913429238493 / 35184372088832 : ℚ) : ℝ) ≤ ((4007307433907944 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (887 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height027.height_factor_upper_887.trans
      change ((51849405 / 140737488355328 : ℚ) : ℝ) ≤ ((103698810 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height027.height_power_upper_887.trans
      change ((2005904320744591 / 140737488355328 : ℚ) : ℝ) ≤ ((4011808641489182 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (888 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height027.height_factor_upper_888.trans
      change ((1580019 / 4398046511104 : ℚ) : ℝ) ≤ ((101121216 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height027.height_power_upper_888.trans
      change ((502038726409445 / 35184372088832 : ℚ) : ℝ) ≤ ((4016309811275560 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (889 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height027.height_factor_upper_889.trans
      change ((98607701 / 281474976710656 : ℚ) : ℝ) ≤ ((98607701 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height027.height_power_upper_889.trans
      change ((502601367911845 / 35184372088832 : ℚ) : ℝ) ≤ ((4020810943294760 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (890 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height027.height_factor_upper_890.trans
      change ((48078337 / 140737488355328 : ℚ) : ℝ) ≤ ((96156674 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height027.height_power_upper_890.trans
      change ((1006328009393609 / 70368744177664 : ℚ) : ℝ) ≤ ((4025312037574436 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (891 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height027.height_factor_upper_891.trans
      change ((93766581 / 281474976710656 : ℚ) : ℝ) ≤ ((93766581 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height027.height_power_upper_891.trans
      change ((2014906547071105 / 140737488355328 : ℚ) : ℝ) ≤ ((4029813094142210 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (892 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height027.height_factor_upper_892.trans
      change ((45717955 / 140737488355328 : ℚ) : ℝ) ≤ ((91435910 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height027.height_power_upper_892.trans
      change ((1008578528256419 / 70368744177664 : ℚ) : ℝ) ≤ ((4034314113025676 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (893 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height027.height_factor_upper_893.trans
      change ((44581591 / 140737488355328 : ℚ) : ℝ) ≤ ((89163182 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height027.height_power_upper_893.trans
      change ((2019407547126197 / 140737488355328 : ℚ) : ℝ) ≤ ((4038815094252394 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (894 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height027.height_factor_upper_894.trans
      change ((43473479 / 140737488355328 : ℚ) : ℝ) ≤ ((86946958 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height027.height_power_upper_894.trans
      change ((4043316037849897 / 281474976710656 : ℚ) : ℝ) ≤ ((4043316037849897 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (895 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height027.height_factor_upper_895.trans
      change ((84785835 / 281474976710656 : ℚ) : ℝ) ≤ ((84785835 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height027.height_power_upper_895.trans
      change ((4047816943845687 / 281474976710656 : ℚ) : ℝ) ≤ ((4047816943845687 : ℕ) : ℝ) / 2^48
      norm_num
end LegendreK6.M2Pilot.FactorBounds.Height027
