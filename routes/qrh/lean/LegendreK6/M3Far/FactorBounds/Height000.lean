import LegendreK6.M3Far.Enclosures.Height000
import LegendreK6.M3FarIntegerData

/-! Join checked analytic enclosures to the exact dyadic witness table. -/
namespace LegendreK6.M3Far.FactorBounds.Height000
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem bounds (i : Fin 125) (hlo : 0 ≤ i.val) (hhi : i.val < 32) :
    heightFactor i ≤ heightDyadicFactor i ∧ heightPower i ≤ heightDyadicPower i := by
  interval_cases hi : i.val
  · have heq : i = (0 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height000.height_factor_upper_0.trans
      change ((271316576601750073 / 140737488355328 : ℚ) : ℝ) ≤ ((542633153203500146 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height000.height_power_upper_0.trans
      change ((7047967639653 / 70368744177664 : ℚ) : ℝ) ≤ ((28191870558612 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height000.height_factor_upper_1.trans
      change ((320664859037327275 / 140737488355328 : ℚ) : ℝ) ≤ ((641329718074654550 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height000.height_power_upper_1.trans
      change ((15932408123783 / 70368744177664 : ℚ) : ℝ) ≤ ((63729632495132 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (2 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height000.height_factor_upper_2.trans
      change ((591780732696578779 / 281474976710656 : ℚ) : ℝ) ≤ ((591780732696578779 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height000.height_power_upper_2.trans
      change ((49633475654735 / 140737488355328 : ℚ) : ℝ) ≤ ((99266951309470 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (3 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height000.height_factor_upper_3.trans
      change ((273028944805986455 / 140737488355328 : ℚ) : ℝ) ≤ ((546057889611972910 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height000.height_power_upper_3.trans
      change ((134803828111513 / 281474976710656 : ℚ) : ℝ) ≤ ((134803828111513 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (4 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height000.height_factor_upper_4.trans
      change ((503865895760563863 / 281474976710656 : ℚ) : ℝ) ≤ ((503865895760563863 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height000.height_power_upper_4.trans
      change ((170340264006983 / 281474976710656 : ℚ) : ℝ) ≤ ((170340264006983 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (5 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height000.height_factor_upper_5.trans
      change ((464932235453528231 / 281474976710656 : ℚ) : ℝ) ≤ ((464932235453528231 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height000.height_power_upper_5.trans
      change ((102938130048729 / 140737488355328 : ℚ) : ℝ) ≤ ((205876260097458 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (6 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height000.height_factor_upper_6.trans
      change ((429005414455213921 / 281474976710656 : ℚ) : ℝ) ≤ ((429005414455213921 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height000.height_power_upper_6.trans
      change ((120705908740197 / 140737488355328 : ℚ) : ℝ) ≤ ((241411817480394 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (7 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height000.height_factor_upper_7.trans
      change ((395853339349042425 / 281474976710656 : ℚ) : ℝ) ≤ ((395853339349042425 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height000.height_power_upper_7.trans
      change ((138473468624571 / 140737488355328 : ℚ) : ℝ) ≤ ((276946937249142 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (8 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height000.height_factor_upper_8.trans
      change ((365261821771063157 / 281474976710656 : ℚ) : ℝ) ≤ ((365261821771063157 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height000.height_power_upper_8.trans
      change ((156240810246487 / 140737488355328 : ℚ) : ℝ) ≤ ((312481620492974 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (9 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height000.height_factor_upper_9.trans
      change ((337033197896167353 / 281474976710656 : ℚ) : ℝ) ≤ ((337033197896167353 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height000.height_power_upper_9.trans
      change ((174007934148549 / 140737488355328 : ℚ) : ℝ) ≤ ((348015868297098 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (10 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height000.height_factor_upper_10.trans
      change ((155492527150934343 / 140737488355328 : ℚ) : ℝ) ≤ ((310985054301868686 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height000.height_power_upper_10.trans
      change ((47943710217835 / 35184372088832 : ℚ) : ℝ) ≤ ((383549681742680 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (11 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height000.height_factor_upper_11.trans
      change ((286949052017557445 / 281474976710656 : ℚ) : ℝ) ≤ ((286949052017557445 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height000.height_power_upper_11.trans
      change ((419083061906865 / 281474976710656 : ℚ) : ℝ) ≤ ((419083061906865 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (12 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height000.height_factor_upper_12.trans
      change ((264769841197607621 / 281474976710656 : ℚ) : ℝ) ≤ ((264769841197607621 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height000.height_power_upper_12.trans
      change ((227308004931399 / 140737488355328 : ℚ) : ℝ) ≤ ((454616009862798 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (13 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height000.height_factor_upper_13.trans
      change ((61076014859674633 / 70368744177664 : ℚ) : ℝ) ≤ ((244304059438698532 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height000.height_power_upper_13.trans
      change ((245074263339819 / 140737488355328 : ℚ) : ℝ) ≤ ((490148526679638 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (14 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height000.height_factor_upper_14.trans
      change ((28177425912366443 / 35184372088832 : ℚ) : ℝ) ≤ ((225419407298931544 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height000.height_power_upper_14.trans
      change ((65710076677823 / 35184372088832 : ℚ) : ℝ) ≤ ((525680613422584 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (15 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height000.height_factor_upper_15.trans
      change ((51998448768054689 / 70368744177664 : ℚ) : ℝ) ≤ ((207993795072218756 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height000.height_power_upper_15.trans
      change ((280606135576447 / 140737488355328 : ℚ) : ℝ) ≤ ((561212271152894 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (16 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height000.height_factor_upper_16.trans
      change ((95957277664585269 / 140737488355328 : ℚ) : ℝ) ≤ ((191914555329170538 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height000.height_power_upper_16.trans
      change ((596743500927899 / 281474976710656 : ℚ) : ℝ) ≤ ((596743500927899 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (17 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height000.height_factor_upper_17.trans
      change ((22134714519780619 / 35184372088832 : ℚ) : ℝ) ≤ ((177077716158244952 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height000.height_power_upper_17.trans
      change ((632274303801029 / 281474976710656 : ℚ) : ℝ) ≤ ((632274303801029 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (18 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height000.height_factor_upper_18.trans
      change ((20423416303868939 / 35184372088832 : ℚ) : ℝ) ≤ ((163387330430951512 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height000.height_power_upper_18.trans
      change ((166951170205457 / 70368744177664 : ℚ) : ℝ) ≤ ((667804680821828 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (19 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height000.height_factor_upper_19.trans
      change ((75377428387461777 / 140737488355328 : ℚ) : ℝ) ≤ ((150754856774923554 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height000.height_power_upper_19.trans
      change ((703334633035973 / 281474976710656 : ℚ) : ℝ) ≤ ((703334633035973 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (20 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height000.height_factor_upper_20.trans
      change ((69549294135497461 / 140737488355328 : ℚ) : ℝ) ≤ ((139098588270994922 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height000.height_power_upper_20.trans
      change ((738864161485297 / 281474976710656 : ℚ) : ℝ) ≤ ((738864161485297 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (21 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height000.height_factor_upper_21.trans
      change ((128343125197167509 / 281474976710656 : ℚ) : ℝ) ≤ ((128343125197167509 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height000.height_power_upper_21.trans
      change ((774393267207803 / 281474976710656 : ℚ) : ℝ) ≤ ((774393267207803 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (22 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height000.height_factor_upper_22.trans
      change ((118418888425502773 / 281474976710656 : ℚ) : ℝ) ≤ ((118418888425502773 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height000.height_power_upper_22.trans
      change ((809921951237685 / 281474976710656 : ℚ) : ℝ) ≤ ((809921951237685 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (23 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height000.height_factor_upper_23.trans
      change ((109261670339327755 / 281474976710656 : ℚ) : ℝ) ≤ ((109261670339327755 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height000.height_power_upper_23.trans
      change ((211362553651337 / 70368744177664 : ℚ) : ℝ) ≤ ((845450214605348 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (24 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height000.height_factor_upper_24.trans
      change ((100812220379390001 / 281474976710656 : ℚ) : ℝ) ≤ ((100812220379390001 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height000.height_power_upper_24.trans
      change ((880978058337423 / 281474976710656 : ℚ) : ℝ) ≤ ((880978058337423 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (25 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height000.height_factor_upper_25.trans
      change ((46507931275136549 / 140737488355328 : ℚ) : ℝ) ≤ ((93015862550273098 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height000.height_power_upper_25.trans
      change ((229126370864197 / 70368744177664 : ℚ) : ℝ) ≤ ((916505483456788 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (26 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height000.height_factor_upper_26.trans
      change ((85822142423923137 / 281474976710656 : ℚ) : ℝ) ≤ ((85822142423923137 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height000.height_power_upper_26.trans
      change ((476016245491293 / 140737488355328 : ℚ) : ℝ) ≤ ((952032490982586 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (27 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height000.height_factor_upper_27.trans
      change ((102452653439087041 / 281474976710656 : ℚ) : ℝ) ≤ ((102452653439087041 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height000.height_power_upper_27.trans
      change ((987559081930243 / 281474976710656 : ℚ) : ℝ) ≤ ((987559081930243 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (28 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height000.height_factor_upper_28.trans
      change ((132154071326937785 / 281474976710656 : ℚ) : ℝ) ≤ ((132154071326937785 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height000.height_power_upper_28.trans
      change ((255771314327871 / 70368744177664 : ℚ) : ℝ) ≤ ((1023085257311484 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (29 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height000.height_factor_upper_29.trans
      change ((53802392335737769 / 140737488355328 : ℚ) : ℝ) ≤ ((107604784671475538 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height000.height_power_upper_29.trans
      change ((264652754533589 / 70368744177664 : ℚ) : ℝ) ≤ ((1058611018134356 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (30 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height000.height_factor_upper_30.trans
      change ((43807768740383475 / 140737488355328 : ℚ) : ℝ) ≤ ((87615537480766950 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height000.height_power_upper_30.trans
      change ((547068182701619 / 140737488355328 : ℚ) : ℝ) ≤ ((1094136365403238 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (31 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height000.height_factor_upper_31.trans
      change ((35669678530138219 / 140737488355328 : ℚ) : ℝ) ≤ ((71339357060276438 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height000.height_power_upper_31.trans
      change ((282415325029717 / 70368744177664 : ℚ) : ℝ) ≤ ((1129661300118868 : ℕ) : ℝ) / 2^48
      norm_num
end LegendreK6.M3Far.FactorBounds.Height000
