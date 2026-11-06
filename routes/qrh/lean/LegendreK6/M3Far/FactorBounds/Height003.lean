import LegendreK6.M3Far.Enclosures.Height003
import LegendreK6.M3FarIntegerData

/-! Join checked analytic enclosures to the exact dyadic witness table. -/
namespace LegendreK6.M3Far.FactorBounds.Height003
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem bounds (i : Fin 125) (hlo : 96 ≤ i.val) (hhi : i.val < 125) :
    heightFactor i ≤ heightDyadicFactor i ∧ heightPower i ≤ heightDyadicPower i := by
  interval_cases hi : i.val
  · have heq : i = (96 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height003.height_factor_upper_96.trans
      change ((27981691477 / 70368744177664 : ℚ) : ℝ) ≤ ((111926765908 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height003.height_power_upper_96.trans
      change ((3437942287267007 / 281474976710656 : ℚ) : ℝ) ≤ ((3437942287267007 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (97 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height003.height_factor_upper_97.trans
      change ((5694718949 / 17592186044416 : ℚ) : ℝ) ≤ ((91115503184 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height003.height_power_upper_97.trans
      change ((3473442037513999 / 281474976710656 : ℚ) : ℝ) ≤ ((3473442037513999 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (98 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height003.height_factor_upper_98.trans
      change ((18543407869 / 70368744177664 : ℚ) : ℝ) ≤ ((74173631476 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height003.height_power_upper_98.trans
      change ((1754470717395759 / 140737488355328 : ℚ) : ℝ) ≤ ((3508941434791518 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (99 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height003.height_factor_upper_99.trans
      change ((60381764415 / 281474976710656 : ℚ) : ℝ) ≤ ((60381764415 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height003.height_power_upper_99.trans
      change ((886110119972191 / 70368744177664 : ℚ) : ℝ) ≤ ((3544440479888764 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (100 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height003.height_factor_upper_100.trans
      change ((49154254283 / 281474976710656 : ℚ) : ℝ) ≤ ((49154254283 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height003.height_power_upper_100.trans
      change ((3579939173592293 / 281474976710656 : ℚ) : ℝ) ≤ ((3579939173592293 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (101 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height003.height_factor_upper_101.trans
      change ((625223915 / 4398046511104 : ℚ) : ℝ) ≤ ((40014330560 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height003.height_power_upper_101.trans
      change ((903859379171507 / 70368744177664 : ℚ) : ℝ) ≤ ((3615437516686028 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (102 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height003.height_factor_upper_102.trans
      change ((4071732479 / 35184372088832 : ℚ) : ℝ) ≤ ((32573859832 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height003.height_power_upper_102.trans
      change ((3650935509951273 / 281474976710656 : ℚ) : ℝ) ≤ ((3650935509951273 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (103 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height003.height_factor_upper_103.trans
      change ((26516868087 / 281474976710656 : ℚ) : ℝ) ≤ ((26516868087 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height003.height_power_upper_103.trans
      change ((1843216577083361 / 140737488355328 : ℚ) : ℝ) ≤ ((3686433154166722 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (104 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height003.height_factor_upper_104.trans
      change ((10793063025 / 140737488355328 : ℚ) : ℝ) ≤ ((21586126050 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height003.height_power_upper_104.trans
      change ((1860965225054237 / 140737488355328 : ℚ) : ℝ) ≤ ((3721930450108474 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (105 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height003.height_factor_upper_105.trans
      change ((4393057049 / 70368744177664 : ℚ) : ℝ) ≤ ((17572228196 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height003.height_power_upper_105.trans
      change ((469678424818755 / 35184372088832 : ℚ) : ℝ) ≤ ((3757427398550040 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (106 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height003.height_factor_upper_106.trans
      change ((7152350965 / 140737488355328 : ℚ) : ℝ) ≤ ((14304701930 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height003.height_power_upper_106.trans
      change ((1896462000131179 / 140737488355328 : ℚ) : ℝ) ≤ ((3792924000262358 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (107 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height003.height_factor_upper_107.trans
      change ((5822384771 / 140737488355328 : ℚ) : ℝ) ≤ ((11644769542 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height003.height_power_upper_107.trans
      change ((3828420256013803 / 281474976710656 : ℚ) : ℝ) ≤ ((3828420256013803 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (108 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height003.height_factor_upper_108.trans
      change ((2369863927 / 70368744177664 : ℚ) : ℝ) ≤ ((9479455708 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height003.height_power_upper_108.trans
      change ((482989520821275 / 35184372088832 : ℚ) : ℝ) ≤ ((3863916166570200 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (109 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height003.height_factor_upper_109.trans
      change ((7716790435 / 281474976710656 : ℚ) : ℝ) ≤ ((7716790435 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height003.height_power_upper_109.trans
      change ((3899411732694833 / 281474976710656 : ℚ) : ℝ) ≤ ((3899411732694833 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (110 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height003.height_factor_upper_110.trans
      change ((6281903787 / 281474976710656 : ℚ) : ℝ) ≤ ((6281903787 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height003.height_power_upper_110.trans
      change ((491863369393557 / 35184372088832 : ℚ) : ℝ) ≤ ((3934906955148456 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (111 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height003.height_factor_upper_111.trans
      change ((5113846641 / 281474976710656 : ℚ) : ℝ) ≤ ((5113846641 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height003.height_power_upper_111.trans
      change ((3970401834689307 / 281474976710656 : ℚ) : ℝ) ≤ ((3970401834689307 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (112 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height003.height_factor_upper_112.trans
      change ((2081501243 / 140737488355328 : ℚ) : ℝ) ≤ ((4163002486 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height003.height_power_upper_112.trans
      change ((4005896372073117 / 281474976710656 : ℚ) : ℝ) ≤ ((4005896372073117 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (113 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height003.height_factor_upper_113.trans
      change ((3388980411 / 281474976710656 : ℚ) : ℝ) ≤ ((3388980411 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height003.height_power_upper_113.trans
      change ((4041390568053121 / 281474976710656 : ℚ) : ℝ) ≤ ((4041390568053121 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (114 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height003.height_factor_upper_114.trans
      change ((2758899805 / 281474976710656 : ℚ) : ℝ) ≤ ((2758899805 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height003.height_power_upper_114.trans
      change ((4076884423380069 / 281474976710656 : ℚ) : ℝ) ≤ ((4076884423380069 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (115 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height003.height_factor_upper_115.trans
      change ((1122996985 / 140737488355328 : ℚ) : ℝ) ≤ ((2245993970 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height003.height_power_upper_115.trans
      change ((64255905293785 / 4398046511104 : ℚ) : ℝ) ≤ ((4112377938802240 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (116 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height003.height_factor_upper_116.trans
      change ((457118337 / 70368744177664 : ℚ) : ℝ) ≤ ((1828473348 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height003.height_power_upper_116.trans
      change ((4147871115065447 / 281474976710656 : ℚ) : ℝ) ≤ ((4147871115065447 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (117 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height003.height_factor_upper_117.trans
      change ((1488600095 / 281474976710656 : ℚ) : ℝ) ≤ ((1488600095 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height003.height_power_upper_117.trans
      change ((4183363952913053 / 281474976710656 : ℚ) : ℝ) ≤ ((4183363952913053 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (118 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height003.height_factor_upper_118.trans
      change ((1211934715 / 281474976710656 : ℚ) : ℝ) ≤ ((1211934715 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height003.height_power_upper_118.trans
      change ((2109428226542989 / 140737488355328 : ℚ) : ℝ) ≤ ((4218856453085978 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (119 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height003.height_factor_upper_119.trans
      change ((986722771 / 281474976710656 : ℚ) : ℝ) ≤ ((986722771 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height003.height_power_upper_119.trans
      change ((2127174308161357 / 140737488355328 : ℚ) : ℝ) ≤ ((4254348616322714 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (120 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height003.height_factor_upper_120.trans
      change ((803395617 / 281474976710656 : ℚ) : ℝ) ≤ ((803395617 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height003.height_power_upper_120.trans
      change ((4289840443359331 / 281474976710656 : ℚ) : ℝ) ≤ ((4289840443359331 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (121 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height003.height_factor_upper_121.trans
      change ((163540991 / 70368744177664 : ℚ) : ℝ) ≤ ((654163964 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height003.height_power_upper_121.trans
      change ((4325331934929489 / 281474976710656 : ℚ) : ℝ) ≤ ((4325331934929489 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (122 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height003.height_factor_upper_122.trans
      change ((532687013 / 281474976710656 : ℚ) : ℝ) ≤ ((532687013 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height003.height_power_upper_122.trans
      change ((1090205772941113 / 70368744177664 : ℚ) : ℝ) ≤ ((4360823091764452 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (123 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height003.height_factor_upper_123.trans
      change ((433803109 / 281474976710656 : ℚ) : ℝ) ≤ ((433803109 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height003.height_power_upper_123.trans
      change ((1099078478648273 / 70368744177664 : ℚ) : ℝ) ≤ ((4396313914593092 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (124 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height003.height_factor_upper_124.trans
      change ((5049318911 / 70368744177664 : ℚ) : ℝ) ≤ ((20197275644 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height003.height_power_upper_124.trans
      change ((4431804404141907 / 281474976710656 : ℚ) : ℝ) ≤ ((4431804404141907 : ℕ) : ℝ) / 2^48
      norm_num
end LegendreK6.M3Far.FactorBounds.Height003
