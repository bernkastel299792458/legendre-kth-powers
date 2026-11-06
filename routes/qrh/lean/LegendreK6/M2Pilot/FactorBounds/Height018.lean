import LegendreK6.M2Pilot.Enclosures.Height018
import LegendreK6.M2PilotIntegerData

/-! Join checked analytic enclosures to the exact dyadic witness table. -/
namespace LegendreK6.M2Pilot.FactorBounds.Height018
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem bounds (i : Fin 988) (hlo : 576 ≤ i.val) (hhi : i.val < 608) :
    heightFactor i ≤ heightDyadicFactor i ∧ heightPower i ≤ heightDyadicPower i := by
  interval_cases hi : i.val
  · have heq : i = (576 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height018.height_factor_upper_576.trans
      change ((257171013981 / 281474976710656 : ℚ) : ℝ) ≤ ((257171013981 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height018.height_power_upper_576.trans
      change ((1304979627706125 / 140737488355328 : ℚ) : ℝ) ≤ ((2609959255412250 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (577 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height018.height_factor_upper_577.trans
      change ((250802157903 / 281474976710656 : ℚ) : ℝ) ≤ ((250802157903 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height018.height_power_upper_577.trans
      change ((2614473686037773 / 281474976710656 : ℚ) : ℝ) ≤ ((2614473686037773 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (578 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height018.height_factor_upper_578.trans
      change ((244590929449 / 281474976710656 : ℚ) : ℝ) ≤ ((244590929449 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height018.height_power_upper_578.trans
      change ((1309494034280373 / 140737488355328 : ℚ) : ℝ) ≤ ((2618988068560746 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (579 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height018.height_factor_upper_579.trans
      change ((119266714935 / 140737488355328 : ℚ) : ℝ) ≤ ((238533429870 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height018.height_power_upper_579.trans
      change ((655875600755229 / 70368744177664 : ℚ) : ℝ) ≤ ((2623502403020916 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (580 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height018.height_factor_upper_580.trans
      change ((116312928391 / 140737488355328 : ℚ) : ℝ) ≤ ((232625856782 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height018.height_power_upper_580.trans
      change ((2628016689457979 / 281474976710656 : ℚ) : ℝ) ≤ ((2628016689457979 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (581 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height018.height_factor_upper_581.trans
      change ((7089515681 / 8796093022208 : ℚ) : ℝ) ≤ ((226864501792 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height018.height_power_upper_581.trans
      change ((82266591497237 / 8796093022208 : ℚ) : ℝ) ≤ ((2632530927911584 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (582 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height018.height_factor_upper_582.trans
      change ((221245748171 / 281474976710656 : ℚ) : ℝ) ≤ ((221245748171 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height018.height_power_upper_582.trans
      change ((164815319901333 / 17592186044416 : ℚ) : ℝ) ≤ ((2637045118421328 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (583 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height018.height_factor_upper_583.trans
      change ((107883034295 / 140737488355328 : ℚ) : ℝ) ≤ ((215766068590 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height018.height_power_upper_583.trans
      change ((2641559261026761 / 281474976710656 : ℚ) : ℝ) ≤ ((2641559261026761 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (584 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height018.height_factor_upper_584.trans
      change ((210422022915 / 281474976710656 : ℚ) : ℝ) ≤ ((210422022915 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height018.height_power_upper_584.trans
      change ((330759169470923 / 35184372088832 : ℚ) : ℝ) ≤ ((2646073355767384 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (585 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height018.height_factor_upper_585.trans
      change ((102605128025 / 140737488355328 : ℚ) : ℝ) ≤ ((205210256050 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height018.height_power_upper_585.trans
      change ((331323425335331 / 35184372088832 : ℚ) : ℝ) ≤ ((2650587402682648 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (586 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height018.height_factor_upper_586.trans
      change ((200127495837 / 281474976710656 : ℚ) : ℝ) ≤ ((200127495837 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height018.height_power_upper_586.trans
      change ((663775350452989 / 70368744177664 : ℚ) : ℝ) ≤ ((2655101401811956 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (587 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height018.height_factor_upper_587.trans
      change ((195170551009 / 281474976710656 : ℚ) : ℝ) ≤ ((195170551009 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height018.height_power_upper_587.trans
      change ((2659615353194663 / 281474976710656 : ℚ) : ℝ) ≤ ((2659615353194663 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (588 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height018.height_factor_upper_588.trans
      change ((95168154595 / 140737488355328 : ℚ) : ℝ) ≤ ((190336309190 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height018.height_power_upper_588.trans
      change ((2664129256870075 / 281474976710656 : ℚ) : ℝ) ≤ ((2664129256870075 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (589 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height018.height_factor_upper_589.trans
      change ((5800679217 / 8796093022208 : ℚ) : ℝ) ≤ ((185621734944 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height018.height_power_upper_589.trans
      change ((2668643112877447 / 281474976710656 : ℚ) : ℝ) ≤ ((2668643112877447 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (590 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height018.height_factor_upper_590.trans
      change ((181023867879 / 281474976710656 : ℚ) : ℝ) ≤ ((181023867879 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height018.height_power_upper_590.trans
      change ((2673156921255991 / 281474976710656 : ℚ) : ℝ) ≤ ((2673156921255991 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (591 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height018.height_factor_upper_591.trans
      change ((176539820789 / 281474976710656 : ℚ) : ℝ) ≤ ((176539820789 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height018.height_power_upper_591.trans
      change ((41838604406951 / 4398046511104 : ℚ) : ℝ) ≤ ((2677670682044864 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (592 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height018.height_factor_upper_592.trans
      change ((172166777849 / 281474976710656 : ℚ) : ℝ) ≤ ((172166777849 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height018.height_power_upper_592.trans
      change ((2682184395283181 / 281474976710656 : ℚ) : ℝ) ≤ ((2682184395283181 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (593 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height018.height_factor_upper_593.trans
      change ((10493874553 / 17592186044416 : ℚ) : ℝ) ≤ ((167901992848 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height018.height_power_upper_593.trans
      change ((671674515252501 / 70368744177664 : ℚ) : ℝ) ≤ ((2686698061010004 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (594 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height018.height_factor_upper_594.trans
      change ((163742787473 / 281474976710656 : ℚ) : ℝ) ≤ ((163742787473 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height018.height_power_upper_594.trans
      change ((1345605839632175 / 140737488355328 : ℚ) : ℝ) ≤ ((2691211679264350 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (595 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height018.height_factor_upper_595.trans
      change ((159686549629 / 281474976710656 : ℚ) : ℝ) ≤ ((159686549629 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height018.height_power_upper_595.trans
      change ((2695725250085185 / 281474976710656 : ℚ) : ℝ) ≤ ((2695725250085185 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (596 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height018.height_factor_upper_596.trans
      change ((77865365901 / 140737488355328 : ℚ) : ℝ) ≤ ((155730731802 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height018.height_power_upper_596.trans
      change ((2700238773511431 / 281474976710656 : ℚ) : ℝ) ≤ ((2700238773511431 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (597 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height018.height_factor_upper_597.trans
      change ((75936424733 / 140737488355328 : ℚ) : ℝ) ≤ ((151872849466 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height018.height_power_upper_597.trans
      change ((2704752249581959 / 281474976710656 : ℚ) : ℝ) ≤ ((2704752249581959 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (598 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height018.height_factor_upper_598.trans
      change ((148110479525 / 281474976710656 : ℚ) : ℝ) ≤ ((148110479525 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height018.height_power_upper_598.trans
      change ((1354632839167797 / 140737488355328 : ℚ) : ℝ) ≤ ((2709265678335594 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (599 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height018.height_factor_upper_599.trans
      change ((36110314699 / 70368744177664 : ℚ) : ℝ) ≤ ((144441258796 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height018.height_power_upper_599.trans
      change ((1356889529905555 / 140737488355328 : ℚ) : ℝ) ≤ ((2713779059811110 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (600 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height018.height_factor_upper_600.trans
      change ((4401965079 / 8796093022208 : ℚ) : ℝ) ≤ ((140862882528 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height018.height_power_upper_600.trans
      change ((1359146197023619 / 140737488355328 : ℚ) : ℝ) ≤ ((2718292394047238 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (601 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height018.height_factor_upper_601.trans
      change ((68686551479 / 140737488355328 : ℚ) : ℝ) ≤ ((137373102958 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height018.height_power_upper_601.trans
      change ((1361402840541329 / 140737488355328 : ℚ) : ℝ) ≤ ((2722805681082658 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (602 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height018.height_factor_upper_602.trans
      change ((133969727905 / 281474976710656 : ℚ) : ℝ) ≤ ((133969727905 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height018.height_power_upper_602.trans
      change ((2727318920956005 / 281474976710656 : ℚ) : ℝ) ≤ ((2727318920956005 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (603 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height018.height_factor_upper_603.trans
      change ((255176991 / 549755813888 : ℚ) : ℝ) ≤ ((130650619392 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height018.height_power_upper_603.trans
      change ((2731832113705863 / 281474976710656 : ℚ) : ℝ) ≤ ((2731832113705863 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (604 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height018.height_factor_upper_604.trans
      change ((15926711539 / 35184372088832 : ℚ) : ℝ) ≤ ((127413692312 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height018.height_power_upper_604.trans
      change ((2736345259370773 / 281474976710656 : ℚ) : ℝ) ≤ ((2736345259370773 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (605 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height018.height_factor_upper_605.trans
      change ((124256913117 / 281474976710656 : ℚ) : ℝ) ≤ ((124256913117 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height018.height_power_upper_605.trans
      change ((1370429178994613 / 140737488355328 : ℚ) : ℝ) ≤ ((2740858357989226 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (606 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height018.height_factor_upper_606.trans
      change ((121178298547 / 281474976710656 : ℚ) : ℝ) ≤ ((121178298547 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height018.height_power_upper_606.trans
      change ((2745371409599667 / 281474976710656 : ℚ) : ℝ) ≤ ((2745371409599667 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (607 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height018.height_factor_upper_607.trans
      change ((7385994649 / 17592186044416 : ℚ) : ℝ) ≤ ((118175914384 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height018.height_power_upper_607.trans
      change ((2749884414240493 / 281474976710656 : ℚ) : ℝ) ≤ ((2749884414240493 : ℕ) : ℝ) / 2^48
      norm_num
end LegendreK6.M2Pilot.FactorBounds.Height018
