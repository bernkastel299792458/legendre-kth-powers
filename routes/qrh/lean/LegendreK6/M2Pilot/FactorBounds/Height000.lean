import LegendreK6.M2Pilot.Enclosures.Height000
import LegendreK6.M2PilotIntegerData

/-! Join checked analytic enclosures to the exact dyadic witness table. -/
namespace LegendreK6.M2Pilot.FactorBounds.Height000
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem bounds (i : Fin 988) (hlo : 0 ≤ i.val) (hhi : i.val < 32) :
    heightFactor i ≤ heightDyadicFactor i ∧ heightPower i ≤ heightDyadicPower i := by
  interval_cases hi : i.val
  · have heq : i = (0 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height000.height_factor_upper_0.trans
      change ((6842520084211003 / 281474976710656 : ℚ) : ℝ) ≤ ((6842520084211003 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height000.height_power_upper_0.trans
      change ((6142020705 / 17592186044416 : ℚ) : ℝ) ≤ ((98272331280 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height000.height_factor_upper_1.trans
      change ((7170742158077399 / 281474976710656 : ℚ) : ℝ) ≤ ((7170742158077399 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height000.height_power_upper_1.trans
      change ((581135851473 / 35184372088832 : ℚ) : ℝ) ≤ ((4649086811784 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (2 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height000.height_factor_upper_2.trans
      change ((3552711160524609 / 140737488355328 : ℚ) : ℝ) ≤ ((7105422321049218 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height000.height_power_upper_2.trans
      change ((2299954605961 / 70368744177664 : ℚ) : ℝ) ≤ ((9199818423844 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (3 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height000.height_factor_upper_3.trans
      change ((7040692665133027 / 281474976710656 : ℚ) : ℝ) ≤ ((7040692665133027 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height000.height_power_upper_3.trans
      change ((13750467257315 / 281474976710656 : ℚ) : ℝ) ≤ ((13750467257315 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (4 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height000.height_factor_upper_4.trans
      change ((1744136976864951 / 70368744177664 : ℚ) : ℝ) ≤ ((6976547907459804 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height000.height_power_upper_4.trans
      change ((1143814587619 / 17592186044416 : ℚ) : ℝ) ≤ ((18301033401904 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (5 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height000.height_factor_upper_5.trans
      change ((3456491405969977 / 140737488355328 : ℚ) : ℝ) ≤ ((6912982811939954 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height000.height_power_upper_5.trans
      change ((2856439618397 / 35184372088832 : ℚ) : ℝ) ≤ ((22851516947176 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (6 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height000.height_factor_upper_6.trans
      change ((6849992188854311 / 281474976710656 : ℚ) : ℝ) ≤ ((6849992188854311 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height000.height_power_upper_6.trans
      change ((27401917982547 / 281474976710656 : ℚ) : ℝ) ≤ ((27401917982547 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (7 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height000.height_factor_upper_7.trans
      change ((6787570894448663 / 281474976710656 : ℚ) : ℝ) ≤ ((6787570894448663 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height000.height_power_upper_7.trans
      change ((31952236597289 / 281474976710656 : ℚ) : ℝ) ≤ ((31952236597289 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (8 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height000.height_factor_upper_8.trans
      change ((6725713830531775 / 281474976710656 : ℚ) : ℝ) ≤ ((6725713830531775 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height000.height_power_upper_8.trans
      change ((18251236440265 / 140737488355328 : ℚ) : ℝ) ≤ ((36502472880530 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (9 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height000.height_factor_upper_9.trans
      change ((6664415944076869 / 281474976710656 : ℚ) : ℝ) ≤ ((6664415944076869 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height000.height_power_upper_9.trans
      change ((41052626921253 / 281474976710656 : ℚ) : ℝ) ≤ ((41052626921253 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (10 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height000.height_factor_upper_10.trans
      change ((6603672226826537 / 281474976710656 : ℚ) : ℝ) ≤ ((6603672226826537 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height000.height_power_upper_10.trans
      change ((22801349404149 / 140737488355328 : ℚ) : ℝ) ≤ ((45602698808298 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (11 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height000.height_factor_upper_11.trans
      change ((1635869428725265 / 70368744177664 : ℚ) : ℝ) ≤ ((6543477714901060 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height000.height_power_upper_11.trans
      change ((50152688630357 / 281474976710656 : ℚ) : ℝ) ≤ ((50152688630357 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (12 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height000.height_factor_upper_12.trans
      change ((1620956872102527 / 70368744177664 : ℚ) : ℝ) ≤ ((6483827488410108 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height000.height_power_upper_12.trans
      change ((3418912279749 / 17592186044416 : ℚ) : ℝ) ≤ ((54702596475984 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (13 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height000.height_factor_upper_13.trans
      change ((1606179167766943 / 70368744177664 : ℚ) : ℝ) ≤ ((6424716671067772 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height000.height_power_upper_13.trans
      change ((59252422433587 / 281474976710656 : ℚ) : ℝ) ≤ ((59252422433587 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (14 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height000.height_factor_upper_14.trans
      change ((3183070214905467 / 140737488355328 : ℚ) : ℝ) ≤ ((6366140429810934 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height000.height_power_upper_14.trans
      change ((63802166591429 / 281474976710656 : ℚ) : ℝ) ≤ ((63802166591429 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (15 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height000.height_factor_upper_15.trans
      change ((394255873401307 / 17592186044416 : ℚ) : ℝ) ≤ ((6308093974420912 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height000.height_power_upper_15.trans
      change ((68351829037635 / 281474976710656 : ℚ) : ℝ) ≤ ((68351829037635 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (16 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height000.height_factor_upper_16.trans
      change ((6250572557148375 / 281474976710656 : ℚ) : ℝ) ≤ ((6250572557148375 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height000.height_power_upper_16.trans
      change ((9112676232523 / 35184372088832 : ℚ) : ℝ) ≤ ((72901409860184 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (17 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height000.height_factor_upper_17.trans
      change ((1548392868085373 / 70368744177664 : ℚ) : ℝ) ≤ ((6193571472341492 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height000.height_power_upper_17.trans
      change ((38725454573457 / 140737488355328 : ℚ) : ℝ) ≤ ((77450909146914 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (18 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height000.height_factor_upper_18.trans
      change ((6137086056077289 / 281474976710656 : ℚ) : ℝ) ≤ ((6137086056077289 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height000.height_power_upper_18.trans
      change ((82000326985523 / 281474976710656 : ℚ) : ℝ) ≤ ((82000326985523 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (19 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height000.height_factor_upper_19.trans
      change ((760138960724523 / 35184372088832 : ℚ) : ℝ) ≤ ((6081111685796184 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height000.height_power_upper_19.trans
      change ((21637415865891 / 70368744177664 : ℚ) : ℝ) ≤ ((86549663463564 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (20 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height000.height_factor_upper_20.trans
      change ((3012821889969839 / 140737488355328 : ℚ) : ℝ) ≤ ((6025643779939678 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height000.height_power_upper_20.trans
      change ((91098918668453 / 281474976710656 : ℚ) : ℝ) ≤ ((91098918668453 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (21 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height000.height_factor_upper_21.trans
      change ((5970677797591173 / 281474976710656 : ℚ) : ℝ) ≤ ((5970677797591173 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height000.height_power_upper_21.trans
      change ((95648092687461 / 281474976710656 : ℚ) : ℝ) ≤ ((95648092687461 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (22 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height000.height_factor_upper_22.trans
      change ((369763077382493 / 17592186044416 : ℚ) : ℝ) ≤ ((5916209238119888 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height000.height_power_upper_22.trans
      change ((100197185607723 / 281474976710656 : ℚ) : ℝ) ≤ ((100197185607723 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (23 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height000.height_factor_upper_23.trans
      change ((5862233640827855 / 281474976710656 : ℚ) : ℝ) ≤ ((5862233640827855 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height000.height_power_upper_23.trans
      change ((52373098758115 / 140737488355328 : ℚ) : ℝ) ≤ ((104746197516230 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (24 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height000.height_factor_upper_24.trans
      change ((5808746584599951 / 281474976710656 : ℚ) : ℝ) ≤ ((5808746584599951 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height000.height_power_upper_24.trans
      change ((109295128499835 / 281474976710656 : ℚ) : ℝ) ≤ ((109295128499835 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (25 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height000.height_factor_upper_25.trans
      change ((5755743687556965 / 281474976710656 : ℚ) : ℝ) ≤ ((5755743687556965 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height000.height_power_upper_25.trans
      change ((113843978645251 / 281474976710656 : ℚ) : ℝ) ≤ ((113843978645251 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (26 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height000.height_factor_upper_26.trans
      change ((5703220606711657 / 281474976710656 : ℚ) : ℝ) ≤ ((5703220606711657 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height000.height_power_upper_26.trans
      change ((29598187009763 / 70368744177664 : ℚ) : ℝ) ≤ ((118392748039052 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (27 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height000.height_factor_upper_27.trans
      change ((5651173037627783 / 281474976710656 : ℚ) : ℝ) ≤ ((5651173037627783 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height000.height_power_upper_27.trans
      change ((15367679595959 / 35184372088832 : ℚ) : ℝ) ≤ ((122941436767672 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (28 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height000.height_factor_upper_28.trans
      change ((2799798357041037 / 140737488355328 : ℚ) : ℝ) ≤ ((5599596714082074 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height000.height_power_upper_28.trans
      change ((3984063903669 / 8796093022208 : ℚ) : ℝ) ≤ ((127490044917408 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (29 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height000.height_factor_upper_29.trans
      change ((5548487407729129 / 281474976710656 : ℚ) : ℝ) ≤ ((5548487407729129 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height000.height_power_upper_29.trans
      change ((132038572574417 / 281474976710656 : ℚ) : ℝ) ≤ ((132038572574417 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (30 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height000.height_factor_upper_30.trans
      change ((2748920463884605 / 140737488355328 : ℚ) : ℝ) ≤ ((5497840927769210 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height000.height_power_upper_30.trans
      change ((68293509912359 / 140737488355328 : ℚ) : ℝ) ≤ ((136587019824718 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (31 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height000.height_factor_upper_31.trans
      change ((2723826560309451 / 140737488355328 : ℚ) : ℝ) ≤ ((5447653120618902 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height000.height_power_upper_31.trans
      change ((141135386754193 / 281474976710656 : ℚ) : ℝ) ≤ ((141135386754193 : ℕ) : ℝ) / 2^48
      norm_num
end LegendreK6.M2Pilot.FactorBounds.Height000
