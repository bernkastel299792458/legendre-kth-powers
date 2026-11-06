import LegendreK6.M3Far.Enclosures.Height001
import LegendreK6.M3FarIntegerData

/-! Join checked analytic enclosures to the exact dyadic witness table. -/
namespace LegendreK6.M3Far.FactorBounds.Height001
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem bounds (i : Fin 125) (hlo : 32 ≤ i.val) (hhi : i.val < 64) :
    heightFactor i ≤ heightDyadicFactor i ∧ heightPower i ≤ heightDyadicPower i := by
  interval_cases hi : i.val
  · have heq : i = (32 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height001.height_factor_upper_32.trans
      change ((29043287578619047 / 140737488355328 : ℚ) : ℝ) ≤ ((58086575157238094 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height001.height_power_upper_32.trans
      change ((1165185823278353 / 281474976710656 : ℚ) : ℝ) ≤ ((1165185823278353 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (33 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height001.height_factor_upper_33.trans
      change ((47295614499798301 / 281474976710656 : ℚ) : ℝ) ≤ ((47295614499798301 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height001.height_power_upper_33.trans
      change ((1200709935875191 / 281474976710656 : ℚ) : ℝ) ≤ ((1200709935875191 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (34 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height001.height_factor_upper_34.trans
      change ((1203412508714401 / 8796093022208 : ℚ) : ℝ) ≤ ((38509200278860832 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height001.height_power_upper_34.trans
      change ((618116819449643 / 140737488355328 : ℚ) : ℝ) ≤ ((1236233638899286 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (35 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height001.height_factor_upper_35.trans
      change ((31354989230288005 / 281474976710656 : ℚ) : ℝ) ≤ ((31354989230288005 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height001.height_power_upper_35.trans
      change ((635878466668483 / 140737488355328 : ℚ) : ℝ) ≤ ((1271756933336966 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (36 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height001.height_factor_upper_36.trans
      change ((25529796012521225 / 281474976710656 : ℚ) : ℝ) ≤ ((25529796012521225 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height001.height_power_upper_36.trans
      change ((653639910085501 / 140737488355328 : ℚ) : ℝ) ≤ ((1307279820171002 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (37 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height001.height_factor_upper_37.trans
      change ((20786748886556387 / 281474976710656 : ℚ) : ℝ) ≤ ((20786748886556387 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height001.height_power_upper_37.trans
      change ((1342802300380621 / 281474976710656 : ℚ) : ℝ) ≤ ((1342802300380621 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (38 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height001.height_factor_upper_38.trans
      change ((16924830738255761 / 281474976710656 : ℚ) : ℝ) ≤ ((16924830738255761 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height001.height_power_upper_38.trans
      change ((172290546867691 / 35184372088832 : ℚ) : ℝ) ≤ ((1378324374941528 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (39 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height001.height_factor_upper_39.trans
      change ((6890181243590191 / 140737488355328 : ℚ) : ℝ) ≤ ((13780362487180382 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height001.height_power_upper_39.trans
      change ((706923022412959 / 140737488355328 : ℚ) : ℝ) ≤ ((1413846044825918 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (40 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height001.height_factor_upper_40.trans
      change ((5610034088437973 / 140737488355328 : ℚ) : ℝ) ≤ ((11220068176875946 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height001.height_power_upper_40.trans
      change ((1449367311002497 / 281474976710656 : ℚ) : ℝ) ≤ ((1449367311002497 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (41 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height001.height_factor_upper_41.trans
      change ((4567714010273327 / 140737488355328 : ℚ) : ℝ) ≤ ((9135428020546654 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height001.height_power_upper_41.trans
      change ((92805510902281 / 17592186044416 : ℚ) : ℝ) ≤ ((1484888174436496 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (42 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height001.height_factor_upper_42.trans
      change ((3719040109327661 / 140737488355328 : ℚ) : ℝ) ≤ ((7438080218655322 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height001.height_power_upper_42.trans
      change ((1520408636089689 / 281474976710656 : ℚ) : ℝ) ≤ ((1520408636089689 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (43 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height001.height_factor_upper_43.trans
      change ((6056076780171877 / 281474976710656 : ℚ) : ℝ) ≤ ((6056076780171877 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height001.height_power_upper_43.trans
      change ((1555928696920409 / 281474976710656 : ℚ) : ℝ) ≤ ((1555928696920409 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (44 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height001.height_factor_upper_44.trans
      change ((4930834747272815 / 281474976710656 : ℚ) : ℝ) ≤ ((4930834747272815 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height001.height_power_upper_44.trans
      change ((1591448357883563 / 281474976710656 : ℚ) : ℝ) ≤ ((1591448357883563 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (45 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height001.height_factor_upper_45.trans
      change ((4014653675502389 / 281474976710656 : ℚ) : ℝ) ≤ ((4014653675502389 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height001.height_power_upper_45.trans
      change ((1626967619930651 / 281474976710656 : ℚ) : ℝ) ≤ ((1626967619930651 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (46 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height001.height_factor_upper_46.trans
      change ((408586775586431 / 35184372088832 : ℚ) : ℝ) ≤ ((3268694204691448 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height001.height_power_upper_46.trans
      change ((415621621002445 / 70368744177664 : ℚ) : ℝ) ≤ ((1662486484009780 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (47 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height001.height_factor_upper_47.trans
      change ((2661332085734311 / 281474976710656 : ℚ) : ℝ) ≤ ((2661332085734311 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height001.height_power_upper_47.trans
      change ((849002475532841 / 140737488355328 : ℚ) : ℝ) ≤ ((1698004951065682 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (48 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height001.height_factor_upper_48.trans
      change ((1083408965780557 / 140737488355328 : ℚ) : ℝ) ≤ ((2166817931561114 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height001.height_power_upper_48.trans
      change ((1733523022039729 / 281474976710656 : ℚ) : ℝ) ≤ ((1733523022039729 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (49 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height001.height_factor_upper_49.trans
      change ((1764185910697509 / 281474976710656 : ℚ) : ℝ) ≤ ((1764185910697509 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height001.height_power_upper_49.trans
      change ((1769040697869947 / 281474976710656 : ℚ) : ℝ) ≤ ((1769040697869947 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (50 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height001.height_factor_upper_50.trans
      change ((1436365147034117 / 281474976710656 : ℚ) : ℝ) ≤ ((1436365147034117 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height001.height_power_upper_50.trans
      change ((1804557979491035 / 281474976710656 : ℚ) : ℝ) ≤ ((1804557979491035 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (51 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height001.height_factor_upper_51.trans
      change ((1169456176379243 / 281474976710656 : ℚ) : ℝ) ≤ ((1169456176379243 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height001.height_power_upper_51.trans
      change ((1840074867834379 / 281474976710656 : ℚ) : ℝ) ≤ ((1840074867834379 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (52 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height001.height_factor_upper_52.trans
      change ((952141802672933 / 281474976710656 : ℚ) : ℝ) ≤ ((952141802672933 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height001.height_power_upper_52.trans
      change ((937795681914035 / 140737488355328 : ℚ) : ℝ) ≤ ((1875591363828070 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (53 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height001.height_factor_upper_53.trans
      change ((387603695256517 / 140737488355328 : ℚ) : ℝ) ≤ ((775207390513034 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height001.height_power_upper_53.trans
      change ((1911107468396915 / 281474976710656 : ℚ) : ℝ) ≤ ((1911107468396915 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (54 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height001.height_factor_upper_54.trans
      change ((315575133508309 / 140737488355328 : ℚ) : ℝ) ≤ ((631150267016618 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height001.height_power_upper_54.trans
      change ((243327897807807 / 35184372088832 : ℚ) : ℝ) ≤ ((1946623182462456 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (55 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height001.height_factor_upper_55.trans
      change ((513861681370875 / 281474976710656 : ℚ) : ℝ) ≤ ((513861681370875 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height001.height_power_upper_55.trans
      change ((1982138506942985 / 281474976710656 : ℚ) : ℝ) ≤ ((1982138506942985 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (56 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height001.height_factor_upper_56.trans
      change ((26147990288339 / 17592186044416 : ℚ) : ℝ) ≤ ((418367844613424 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height001.height_power_upper_56.trans
      change ((2017653442753557 / 281474976710656 : ℚ) : ℝ) ≤ ((2017653442753557 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (57 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height001.height_factor_upper_57.trans
      change ((170309537714435 / 140737488355328 : ℚ) : ℝ) ≤ ((340619075428870 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height001.height_power_upper_57.trans
      change ((2053167990806009 / 281474976710656 : ℚ) : ℝ) ≤ ((2053167990806009 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (58 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height001.height_factor_upper_58.trans
      change ((277318116084111 / 281474976710656 : ℚ) : ℝ) ≤ ((277318116084111 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height001.height_power_upper_58.trans
      change ((2088682152008971 / 281474976710656 : ℚ) : ℝ) ≤ ((2088682152008971 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (59 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height001.height_factor_upper_59.trans
      change ((225780342388287 / 281474976710656 : ℚ) : ℝ) ≤ ((225780342388287 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height001.height_power_upper_59.trans
      change ((2124195927267885 / 281474976710656 : ℚ) : ℝ) ≤ ((2124195927267885 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (60 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height001.height_factor_upper_60.trans
      change ((183819943060417 / 281474976710656 : ℚ) : ℝ) ≤ ((183819943060417 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height001.height_power_upper_60.trans
      change ((269963664685627 / 35184372088832 : ℚ) : ℝ) ≤ ((2159709317485016 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (61 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height001.height_factor_upper_61.trans
      change ((149657244368715 / 281474976710656 : ℚ) : ℝ) ≤ ((149657244368715 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height001.height_power_upper_61.trans
      change ((1097611161779735 / 140737488355328 : ℚ) : ℝ) ≤ ((2195222323559470 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (62 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height001.height_factor_upper_62.trans
      change ((3807601624655 / 8796093022208 : ℚ) : ℝ) ≤ ((121843251988960 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height001.height_power_upper_62.trans
      change ((2230734946387207 / 281474976710656 : ℚ) : ℝ) ≤ ((2230734946387207 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (63 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height001.height_factor_upper_63.trans
      change ((99198211676265 / 281474976710656 : ℚ) : ℝ) ≤ ((99198211676265 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height001.height_power_upper_63.trans
      change ((2266247186861055 / 281474976710656 : ℚ) : ℝ) ≤ ((2266247186861055 : ℕ) : ℝ) / 2^48
      norm_num
end LegendreK6.M3Far.FactorBounds.Height001
