import LegendreK6.M2Pilot.Enclosures.Height029
import LegendreK6.M2PilotIntegerData

/-! Join checked analytic enclosures to the exact dyadic witness table. -/
namespace LegendreK6.M2Pilot.FactorBounds.Height029
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem bounds (i : Fin 988) (hlo : 928 ≤ i.val) (hhi : i.val < 960) :
    heightFactor i ≤ heightDyadicFactor i ∧ heightPower i ≤ heightDyadicPower i := by
  interval_cases hi : i.val
  · have heq : i = (928 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height029.height_factor_upper_928.trans
      change ((36955701 / 281474976710656 : ℚ) : ℝ) ≤ ((36955701 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height029.height_power_upper_928.trans
      change ((2098162962692677 / 140737488355328 : ℚ) : ℝ) ≤ ((4196325925385354 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (929 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height029.height_factor_upper_929.trans
      change ((4504713 / 35184372088832 : ℚ) : ℝ) ≤ ((36037704 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height029.height_power_upper_929.trans
      change ((4200825569073779 / 281474976710656 : ℚ) : ℝ) ≤ ((4200825569073779 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (930 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height029.height_factor_upper_930.trans
      change ((8785635 / 70368744177664 : ℚ) : ℝ) ≤ ((35142540 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height029.height_power_upper_930.trans
      change ((1051331294026093 / 70368744177664 : ℚ) : ℝ) ≤ ((4205325176104372 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (931 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height029.height_factor_upper_931.trans
      change ((17134821 / 140737488355328 : ℚ) : ℝ) ≤ ((34269642 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height029.height_power_upper_931.trans
      change ((2104912373251789 / 140737488355328 : ℚ) : ℝ) ≤ ((4209824746503578 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (932 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height029.height_factor_upper_932.trans
      change ((4177307 / 35184372088832 : ℚ) : ℝ) ≤ ((33418456 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height029.height_power_upper_932.trans
      change ((4214324280297811 / 281474976710656 : ℚ) : ℝ) ≤ ((4214324280297811 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (933 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height029.height_factor_upper_933.trans
      change ((16294221 / 140737488355328 : ℚ) : ℝ) ≤ ((32588442 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height029.height_power_upper_933.trans
      change ((4218823777513459 / 281474976710656 : ℚ) : ℝ) ≤ ((4218823777513459 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (934 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height029.height_factor_upper_934.trans
      change ((31779075 / 281474976710656 : ℚ) : ℝ) ≤ ((31779075 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height029.height_power_upper_934.trans
      change ((263957702386055 / 17592186044416 : ℚ) : ℝ) ≤ ((4223323238176880 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (935 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height029.height_factor_upper_935.trans
      change ((30989839 / 281474976710656 : ℚ) : ℝ) ≤ ((30989839 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height029.height_power_upper_935.trans
      change ((1056955665578601 / 70368744177664 : ℚ) : ℝ) ≤ ((4227822662314404 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (936 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height029.height_factor_upper_936.trans
      change ((7555059 / 70368744177664 : ℚ) : ℝ) ≤ ((30220236 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height029.height_power_upper_936.trans
      change ((4232322049952331 / 281474976710656 : ℚ) : ℝ) ≤ ((4232322049952331 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (937 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height029.height_factor_upper_937.trans
      change ((29469777 / 281474976710656 : ℚ) : ℝ) ≤ ((29469777 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height029.height_power_upper_937.trans
      change ((4236821401116935 / 281474976710656 : ℚ) : ℝ) ≤ ((4236821401116935 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (938 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height029.height_factor_upper_938.trans
      change ((14368993 / 140737488355328 : ℚ) : ℝ) ≤ ((28737986 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height029.height_power_upper_938.trans
      change ((4241320715834459 / 281474976710656 : ℚ) : ℝ) ≤ ((4241320715834459 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (939 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height029.height_factor_upper_939.trans
      change ((28024399 / 281474976710656 : ℚ) : ℝ) ≤ ((28024399 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height029.height_power_upper_939.trans
      change ((2122909997065561 / 140737488355328 : ℚ) : ℝ) ≤ ((4245819994131122 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (940 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height029.height_factor_upper_940.trans
      change ((27328563 / 281474976710656 : ℚ) : ℝ) ≤ ((27328563 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height029.height_power_upper_940.trans
      change ((4250319236033109 / 281474976710656 : ℚ) : ℝ) ≤ ((4250319236033109 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (941 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height029.height_factor_upper_941.trans
      change ((26650037 / 281474976710656 : ℚ) : ℝ) ≤ ((26650037 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height029.height_power_upper_941.trans
      change ((2127409220783291 / 140737488355328 : ℚ) : ℝ) ≤ ((4254818441566582 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (942 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height029.height_factor_upper_942.trans
      change ((12994195 / 140737488355328 : ℚ) : ℝ) ≤ ((25988390 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height029.height_power_upper_942.trans
      change ((4259317610757671 / 281474976710656 : ℚ) : ℝ) ≤ ((4259317610757671 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (943 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height029.height_factor_upper_943.trans
      change ((25343203 / 281474976710656 : ℚ) : ℝ) ≤ ((25343203 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height029.height_power_upper_943.trans
      change ((4263816743632479 / 281474976710656 : ℚ) : ℝ) ≤ ((4263816743632479 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (944 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height029.height_factor_upper_944.trans
      change ((24714067 / 281474976710656 : ℚ) : ℝ) ≤ ((24714067 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height029.height_power_upper_944.trans
      change ((4268315840217083 / 281474976710656 : ℚ) : ℝ) ≤ ((4268315840217083 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (945 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height029.height_factor_upper_945.trans
      change ((24100581 / 281474976710656 : ℚ) : ℝ) ≤ ((24100581 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height029.height_power_upper_945.trans
      change ((4272814900537529 / 281474976710656 : ℚ) : ℝ) ≤ ((4272814900537529 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (946 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height029.height_factor_upper_946.trans
      change ((11751179 / 140737488355328 : ℚ) : ℝ) ≤ ((23502358 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height029.height_power_upper_946.trans
      change ((4277313924619837 / 281474976710656 : ℚ) : ℝ) ≤ ((4277313924619837 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (947 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height029.height_factor_upper_947.trans
      change ((11459509 / 140737488355328 : ℚ) : ℝ) ≤ ((22919018 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height029.height_power_upper_947.trans
      change ((1070453228122499 / 70368744177664 : ℚ) : ℝ) ≤ ((4281812912489996 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (948 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height029.height_factor_upper_948.trans
      change ((22350191 / 281474976710656 : ℚ) : ℝ) ≤ ((22350191 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height029.height_power_upper_948.trans
      change ((1071577966043493 / 70368744177664 : ℚ) : ℝ) ≤ ((4286311864173972 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (949 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height029.height_factor_upper_949.trans
      change ((21795515 / 281474976710656 : ℚ) : ℝ) ≤ ((21795515 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height029.height_power_upper_949.trans
      change ((2145405389848849 / 140737488355328 : ℚ) : ℝ) ≤ ((4290810779697698 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (950 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height029.height_factor_upper_950.trans
      change ((10627319 / 140737488355328 : ℚ) : ℝ) ≤ ((21254638 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height029.height_power_upper_950.trans
      change ((4295309659087083 / 281474976710656 : ℚ) : ℝ) ≤ ((4295309659087083 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (951 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height029.height_factor_upper_951.trans
      change ((20727219 / 281474976710656 : ℚ) : ℝ) ≤ ((20727219 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height029.height_power_upper_951.trans
      change ((2149904251184003 / 140737488355328 : ℚ) : ℝ) ≤ ((4299808502368006 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (952 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height029.height_factor_upper_952.trans
      change ((20212921 / 281474976710656 : ℚ) : ℝ) ≤ ((20212921 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height029.height_power_upper_952.trans
      change ((2152153654783159 / 140737488355328 : ℚ) : ℝ) ≤ ((4304307309566318 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (953 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height029.height_factor_upper_953.trans
      change ((4927855 / 70368744177664 : ℚ) : ℝ) ≤ ((19711420 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height029.height_power_upper_953.trans
      change ((1077201520176961 / 70368744177664 : ℚ) : ℝ) ≤ ((4308806080707844 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (954 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height029.height_factor_upper_954.trans
      change ((19222395 / 281474976710656 : ℚ) : ℝ) ≤ ((19222395 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height029.height_power_upper_954.trans
      change ((1078326203954595 / 70368744177664 : ℚ) : ℝ) ≤ ((4313304815818380 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (955 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height029.height_factor_upper_955.trans
      change ((9372769 / 140737488355328 : ℚ) : ℝ) ≤ ((18745538 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height029.height_power_upper_955.trans
      change ((4317803514923695 / 281474976710656 : ℚ) : ℝ) ≤ ((4317803514923695 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (956 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height029.height_factor_upper_956.trans
      change ((9140273 / 140737488355328 : ℚ) : ℝ) ≤ ((18280546 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height029.height_power_upper_956.trans
      change ((4322302178049529 / 281474976710656 : ℚ) : ℝ) ≤ ((4322302178049529 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (957 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height029.height_factor_upper_957.trans
      change ((17827123 / 281474976710656 : ℚ) : ℝ) ≤ ((17827123 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height029.height_power_upper_957.trans
      change ((1081700201305399 / 70368744177664 : ℚ) : ℝ) ≤ ((4326800805221596 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (958 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height029.height_factor_upper_958.trans
      change ((8692491 / 140737488355328 : ℚ) : ℝ) ≤ ((17384982 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height029.height_power_upper_958.trans
      change ((2165649698232791 / 140737488355328 : ℚ) : ℝ) ≤ ((4331299396465582 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (959 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height029.height_factor_upper_959.trans
      change ((8476921 / 140737488355328 : ℚ) : ℝ) ≤ ((16953842 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height029.height_power_upper_959.trans
      change ((2167898975903573 / 140737488355328 : ℚ) : ℝ) ≤ ((4335797951807146 : ℕ) : ℝ) / 2^48
      norm_num
end LegendreK6.M2Pilot.FactorBounds.Height029
