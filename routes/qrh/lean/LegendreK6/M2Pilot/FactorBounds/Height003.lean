import LegendreK6.M2Pilot.Enclosures.Height003
import LegendreK6.M2PilotIntegerData

/-! Join checked analytic enclosures to the exact dyadic witness table. -/
namespace LegendreK6.M2Pilot.FactorBounds.Height003
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem bounds (i : Fin 988) (hlo : 96 ≤ i.val) (hhi : i.val < 128) :
    heightFactor i ≤ heightDyadicFactor i ∧ heightPower i ≤ heightDyadicPower i := by
  interval_cases hi : i.val
  · have heq : i = (96 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height003.height_factor_upper_96.trans
      change ((1498637345146289 / 140737488355328 : ℚ) : ℝ) ≤ ((2997274690292578 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height003.height_power_upper_96.trans
      change ((218305477070525 / 140737488355328 : ℚ) : ℝ) ≤ ((436610954141050 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (97 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height003.height_factor_upper_97.trans
      change ((742446912841387 / 70368744177664 : ℚ) : ℝ) ≤ ((2969787651365548 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height003.height_power_upper_97.trans
      change ((441154203119501 / 281474976710656 : ℚ) : ℝ) ≤ ((441154203119501 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (98 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height003.height_factor_upper_98.trans
      change ((1471275430507367 / 140737488355328 : ℚ) : ℝ) ≤ ((2942550861014734 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height003.height_power_upper_98.trans
      change ((445697377232021 / 281474976710656 : ℚ) : ℝ) ≤ ((445697377232021 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (99 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height003.height_factor_upper_99.trans
      change ((1457781029827119 / 140737488355328 : ℚ) : ℝ) ≤ ((2915562059654238 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height003.height_power_upper_99.trans
      change ((450240476555771 / 281474976710656 : ℚ) : ℝ) ≤ ((450240476555771 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (100 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height003.height_factor_upper_100.trans
      change ((722204751977103 / 70368744177664 : ℚ) : ℝ) ≤ ((2888819007908412 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height003.height_power_upper_100.trans
      change ((227391750583897 / 140737488355328 : ℚ) : ℝ) ≤ ((454783501167794 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (101 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height003.height_factor_upper_101.trans
      change ((2862319486433065 / 281474976710656 : ℚ) : ℝ) ≤ ((2862319486433065 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height003.height_power_upper_101.trans
      change ((114831612786253 / 70368744177664 : ℚ) : ℝ) ≤ ((459326451145012 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (102 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height003.height_factor_upper_102.trans
      change ((2836061295738243 / 281474976710656 : ℚ) : ℝ) ≤ ((2836061295738243 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height003.height_power_upper_102.trans
      change ((231934663282115 / 140737488355328 : ℚ) : ℝ) ≤ ((463869326564230 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (103 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height003.height_factor_upper_103.trans
      change ((10976727562549 / 1099511627776 : ℚ) : ℝ) ≤ ((2810042256012544 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height003.height_power_upper_103.trans
      change ((468412127502135 / 281474976710656 : ℚ) : ℝ) ≤ ((468412127502135 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (104 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height003.height_factor_upper_104.trans
      change ((2784260206948975 / 281474976710656 : ℚ) : ℝ) ≤ ((2784260206948975 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height003.height_power_upper_104.trans
      change ((236477427017647 / 140737488355328 : ℚ) : ℝ) ≤ ((472954854035294 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (105 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height003.height_factor_upper_105.trans
      change ((172419562973271 / 17592186044416 : ℚ) : ℝ) ≤ ((2758713007572336 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height003.height_power_upper_105.trans
      change ((477497506240157 / 281474976710656 : ℚ) : ℝ) ≤ ((477497506240157 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (106 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height003.height_factor_upper_106.trans
      change ((1366699268034047 / 140737488355328 : ℚ) : ℝ) ≤ ((2733398536068094 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height003.height_power_upper_106.trans
      change ((15063752631033 / 8796093022208 : ℚ) : ℝ) ≤ ((482040084193056 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (107 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height003.height_factor_upper_107.trans
      change ((338539336201597 / 35184372088832 : ℚ) : ℝ) ≤ ((2708314689612776 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height003.height_power_upper_107.trans
      change ((486582587970205 / 281474976710656 : ℚ) : ℝ) ≤ ((486582587970205 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (108 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height003.height_factor_upper_108.trans
      change ((2683459384205823 / 281474976710656 : ℚ) : ℝ) ≤ ((2683459384205823 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height003.height_power_upper_108.trans
      change ((491125017647701 / 281474976710656 : ℚ) : ℝ) ≤ ((491125017647701 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (109 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height003.height_factor_upper_109.trans
      change ((1329415277251463 / 140737488355328 : ℚ) : ℝ) ≤ ((2658830554502926 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height003.height_power_upper_109.trans
      change ((247833686650763 / 140737488355328 : ℚ) : ℝ) ≤ ((495667373301526 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (110 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height003.height_factor_upper_110.trans
      change ((658606538412705 / 70368744177664 : ℚ) : ℝ) ≤ ((2634426153650820 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height003.height_power_upper_110.trans
      change ((500209655007541 / 281474976710656 : ℚ) : ℝ) ≤ ((500209655007541 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (111 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height003.height_factor_upper_111.trans
      change ((2610244153123509 / 281474976710656 : ℚ) : ℝ) ≤ ((2610244153123509 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height003.height_power_upper_111.trans
      change ((504751862841495 / 281474976710656 : ℚ) : ℝ) ≤ ((504751862841495 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (112 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height003.height_factor_upper_112.trans
      change ((1293141271279971 / 140737488355328 : ℚ) : ℝ) ≤ ((2586282542559942 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height003.height_power_upper_112.trans
      change ((63661749609877 / 35184372088832 : ℚ) : ℝ) ≤ ((509293996879016 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (113 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height003.height_factor_upper_113.trans
      change ((2562539329603093 / 281474976710656 : ℚ) : ℝ) ≤ ((2562539329603093 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height003.height_power_upper_113.trans
      change ((513836057195621 / 281474976710656 : ℚ) : ℝ) ≤ ((513836057195621 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (114 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height003.height_factor_upper_114.trans
      change ((2539012539740457 / 281474976710656 : ℚ) : ℝ) ≤ ((2539012539740457 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height003.height_power_upper_114.trans
      change ((518378043866707 / 281474976710656 : ℚ) : ℝ) ≤ ((518378043866707 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (115 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height003.height_factor_upper_115.trans
      change ((1257850108072969 / 140737488355328 : ℚ) : ℝ) ≤ ((2515700216145938 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height003.height_power_upper_115.trans
      change ((522919956967557 / 281474976710656 : ℚ) : ℝ) ≤ ((522919956967557 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (116 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height003.height_factor_upper_116.trans
      change ((1246300209761561 / 140737488355328 : ℚ) : ℝ) ≤ ((2492600419523122 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height003.height_power_upper_116.trans
      change ((527461796573339 / 281474976710656 : ℚ) : ℝ) ≤ ((527461796573339 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (117 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height003.height_factor_upper_117.trans
      change ((2469711227949917 / 281474976710656 : ℚ) : ℝ) ≤ ((2469711227949917 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height003.height_power_upper_117.trans
      change ((532003562759105 / 281474976710656 : ℚ) : ℝ) ≤ ((532003562759105 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (118 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height003.height_factor_upper_118.trans
      change ((2447030736724563 / 281474976710656 : ℚ) : ℝ) ≤ ((2447030736724563 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height003.height_power_upper_118.trans
      change ((536545255599793 / 281474976710656 : ℚ) : ℝ) ≤ ((536545255599793 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (119 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height003.height_factor_upper_119.trans
      change ((151534816138311 / 17592186044416 : ℚ) : ℝ) ≤ ((2424557058212976 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height003.height_power_upper_119.trans
      change ((270543437585113 / 140737488355328 : ℚ) : ℝ) ≤ ((541086875170226 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (120 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height003.height_factor_upper_120.trans
      change ((2402288321697439 / 281474976710656 : ℚ) : ℝ) ≤ ((2402288321697439 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height003.height_power_upper_120.trans
      change ((545628421545111 / 281474976710656 : ℚ) : ℝ) ≤ ((545628421545111 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (121 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height003.height_factor_upper_121.trans
      change ((2380222673226611 / 281474976710656 : ℚ) : ℝ) ≤ ((2380222673226611 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height003.height_power_upper_121.trans
      change ((137542473699761 / 70368744177664 : ℚ) : ℝ) ≤ ((550169894799044 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (122 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height003.height_factor_upper_122.trans
      change ((1179179137733429 / 140737488355328 : ℚ) : ℝ) ≤ ((2358358275466858 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height003.height_power_upper_122.trans
      change ((554711295006503 / 281474976710656 : ℚ) : ℝ) ≤ ((554711295006503 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (123 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height003.height_factor_upper_123.trans
      change ((292086663444359 / 35184372088832 : ℚ) : ℝ) ≤ ((2336693307554872 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height003.height_power_upper_123.trans
      change ((559252622241857 / 281474976710656 : ℚ) : ℝ) ≤ ((559252622241857 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (124 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height003.height_factor_upper_124.trans
      change ((578806491237899 / 70368744177664 : ℚ) : ℝ) ≤ ((2315225964951596 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height003.height_power_upper_124.trans
      change ((281896938289679 / 140737488355328 : ℚ) : ℝ) ≤ ((563793876579358 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (125 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height003.height_factor_upper_125.trans
      change ((286744307412177 / 35184372088832 : ℚ) : ℝ) ≤ ((2293954459297416 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height003.height_power_upper_125.trans
      change ((568335058093145 / 281474976710656 : ℚ) : ℝ) ≤ ((568335058093145 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (126 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height003.height_factor_upper_126.trans
      change ((1136438509134315 / 140737488355328 : ℚ) : ℝ) ≤ ((2272877018268630 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height003.height_power_upper_126.trans
      change ((572876166857245 / 281474976710656 : ℚ) : ℝ) ≤ ((572876166857245 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (127 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height003.height_factor_upper_127.trans
      change ((2251991885435173 / 281474976710656 : ℚ) : ℝ) ≤ ((2251991885435173 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height003.height_power_upper_127.trans
      change ((144354300736393 / 70368744177664 : ℚ) : ℝ) ≤ ((577417202945572 : ℕ) : ℝ) / 2^48
      norm_num
end LegendreK6.M2Pilot.FactorBounds.Height003
