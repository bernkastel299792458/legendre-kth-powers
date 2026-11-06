import LegendreK6.M2Pilot.Enclosures.Height002
import LegendreK6.M2PilotIntegerData

/-! Join checked analytic enclosures to the exact dyadic witness table. -/
namespace LegendreK6.M2Pilot.FactorBounds.Height002
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem bounds (i : Fin 988) (hlo : 64 ≤ i.val) (hhi : i.val < 96) :
    heightFactor i ≤ heightDyadicFactor i ∧ heightPower i ≤ heightDyadicPower i := by
  interval_cases hi : i.val
  · have heq : i = (64 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height002.height_factor_upper_64.trans
      change ((3929337854053 / 274877906944 : ℚ) : ℝ) ≤ ((4023641962550272 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height002.height_power_upper_64.trans
      change ((291186989547595 / 281474976710656 : ℚ) : ℝ) ≤ ((291186989547595 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (65 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height002.height_factor_upper_65.trans
      change ((3986822987103729 / 281474976710656 : ℚ) : ℝ) ≤ ((3986822987103729 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height002.height_power_upper_65.trans
      change ((295732675703685 / 281474976710656 : ℚ) : ℝ) ≤ ((295732675703685 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (66 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height002.height_factor_upper_66.trans
      change ((3950338394942673 / 281474976710656 : ℚ) : ℝ) ≤ ((3950338394942673 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height002.height_power_upper_66.trans
      change ((150139142230109 / 140737488355328 : ℚ) : ℝ) ≤ ((300278284460218 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (67 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height002.height_factor_upper_67.trans
      change ((3914185175262905 / 281474976710656 : ℚ) : ℝ) ≤ ((3914185175262905 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height002.height_power_upper_67.trans
      change ((304823815898307 / 281474976710656 : ℚ) : ℝ) ≤ ((304823815898307 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (68 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height002.height_factor_upper_68.trans
      change ((969590086025665 / 70368744177664 : ℚ) : ℝ) ≤ ((3878360344102660 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height002.height_power_upper_68.trans
      change ((154684635049467 / 140737488355328 : ℚ) : ℝ) ≤ ((309369270098934 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (69 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height002.height_factor_upper_69.trans
      change ((3842860944106039 / 281474976710656 : ℚ) : ℝ) ≤ ((3842860944106039 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height002.height_power_upper_69.trans
      change ((156957323571477 / 140737488355328 : ℚ) : ℝ) ≤ ((313914647142954 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (70 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height002.height_factor_upper_70.trans
      change ((3807684044288503 / 281474976710656 : ℚ) : ℝ) ≤ ((3807684044288503 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height002.height_power_upper_70.trans
      change ((318459947111097 / 281474976710656 : ℚ) : ℝ) ≤ ((318459947111097 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (71 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height002.height_factor_upper_71.trans
      change ((235801671237775 / 17592186044416 : ℚ) : ℝ) ≤ ((3772826739804400 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height002.height_power_upper_71.trans
      change ((323005170083965 / 281474976710656 : ℚ) : ℝ) ≤ ((323005170083965 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (72 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height002.height_factor_upper_72.trans
      change ((934571537929129 / 70368744177664 : ℚ) : ℝ) ≤ ((3738286151716516 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height002.height_power_upper_72.trans
      change ((163775158071017 / 140737488355328 : ℚ) : ℝ) ≤ ((327550316142034 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (73 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height002.height_factor_upper_73.trans
      change ((3704059426767635 / 281474976710656 : ℚ) : ℝ) ≤ ((3704059426767635 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height002.height_power_upper_73.trans
      change ((332095385365653 / 281474976710656 : ℚ) : ℝ) ≤ ((332095385365653 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (74 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height002.height_factor_upper_74.trans
      change ((3670143737154079 / 281474976710656 : ℚ) : ℝ) ≤ ((3670143737154079 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height002.height_power_upper_74.trans
      change ((336640377835047 / 281474976710656 : ℚ) : ℝ) ≤ ((336640377835047 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (75 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height002.height_factor_upper_75.trans
      change ((3636536280301221 / 281474976710656 : ℚ) : ℝ) ≤ ((3636536280301221 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height002.height_power_upper_75.trans
      change ((341185293630313 / 281474976710656 : ℚ) : ℝ) ≤ ((341185293630313 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (76 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height002.height_factor_upper_76.trans
      change ((3603234278640953 / 281474976710656 : ℚ) : ℝ) ≤ ((3603234278640953 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height002.height_power_upper_76.trans
      change ((345730132831425 / 281474976710656 : ℚ) : ℝ) ≤ ((345730132831425 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (77 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height002.height_factor_upper_77.trans
      change ((3570234979391089 / 281474976710656 : ℚ) : ℝ) ≤ ((3570234979391089 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height002.height_power_upper_77.trans
      change ((175137447759115 / 140737488355328 : ℚ) : ℝ) ≤ ((350274895518230 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (78 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height002.height_factor_upper_78.trans
      change ((1768767827168343 / 140737488355328 : ℚ) : ℝ) ≤ ((3537535654336686 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height002.height_power_upper_78.trans
      change ((354819581770453 / 281474976710656 : ℚ) : ℝ) ≤ ((354819581770453 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (79 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height002.height_factor_upper_79.trans
      change ((3505133599613275 / 281474976710656 : ℚ) : ℝ) ≤ ((3505133599613275 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height002.height_power_upper_79.trans
      change ((359364191667691 / 281474976710656 : ℚ) : ℝ) ≤ ((359364191667691 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (80 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height002.height_factor_upper_80.trans
      change ((27133016683531 / 2199023255552 : ℚ) : ℝ) ≤ ((3473026135491968 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height002.height_power_upper_80.trans
      change ((363908725289419 / 281474976710656 : ℚ) : ℝ) ≤ ((363908725289419 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (81 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height002.height_factor_upper_81.trans
      change ((1720605303083225 / 140737488355328 : ℚ) : ℝ) ≤ ((3441210606166450 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height002.height_power_upper_81.trans
      change ((368453182714987 / 281474976710656 : ℚ) : ℝ) ≤ ((368453182714987 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (82 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height002.height_factor_upper_82.trans
      change ((3409684379541815 / 281474976710656 : ℚ) : ℝ) ≤ ((3409684379541815 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height002.height_power_upper_82.trans
      change ((372997564023621 / 281474976710656 : ℚ) : ℝ) ≤ ((372997564023621 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (83 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height002.height_factor_upper_83.trans
      change ((844611211756311 / 70368744177664 : ℚ) : ℝ) ≤ ((3378444847025244 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height002.height_power_upper_83.trans
      change ((188770934647213 / 140737488355328 : ℚ) : ℝ) ≤ ((377541869294426 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (84 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height002.height_factor_upper_84.trans
      change ((3347489423318511 / 281474976710656 : ℚ) : ℝ) ≤ ((3347489423318511 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height002.height_power_upper_84.trans
      change ((95521524651595 / 70368744177664 : ℚ) : ℝ) ≤ ((382086098606380 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (85 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height002.height_factor_upper_85.trans
      change ((3316815546212291 / 281474976710656 : ℚ) : ℝ) ≤ ((3316815546212291 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height002.height_power_upper_85.trans
      change ((386630252038341 / 281474976710656 : ℚ) : ℝ) ≤ ((386630252038341 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (86 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height002.height_factor_upper_86.trans
      change ((3286420676382263 / 281474976710656 : ℚ) : ℝ) ≤ ((3286420676382263 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height002.height_power_upper_86.trans
      change ((391174329669043 / 281474976710656 : ℚ) : ℝ) ≤ ((391174329669043 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (87 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height002.height_factor_upper_87.trans
      change ((3256302297186989 / 281474976710656 : ℚ) : ℝ) ≤ ((3256302297186989 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height002.height_power_upper_87.trans
      change ((49464791447137 / 35184372088832 : ℚ) : ℝ) ≤ ((395718331577096 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (88 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height002.height_factor_upper_88.trans
      change ((3226457914467553 / 281474976710656 : ℚ) : ℝ) ≤ ((3226457914467553 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height002.height_power_upper_88.trans
      change ((12508195557531 / 8796093022208 : ℚ) : ℝ) ≤ ((400262257840992 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (89 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height002.height_factor_upper_89.trans
      change ((1598442528174477 / 140737488355328 : ℚ) : ℝ) ≤ ((3196885056348954 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height002.height_power_upper_89.trans
      change ((50600763567387 / 35184372088832 : ℚ) : ℝ) ≤ ((404806108539096 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (90 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height002.height_factor_upper_90.trans
      change ((1583790636521609 / 140737488355328 : ℚ) : ℝ) ≤ ((3167581273043218 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height002.height_power_upper_90.trans
      change ((51168735468707 / 35184372088832 : ℚ) : ℝ) ≤ ((409349883749656 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (91 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height002.height_factor_upper_91.trans
      change ((98079504270445 / 8796093022208 : ℚ) : ℝ) ≤ ((3138544136654240 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height002.height_power_upper_91.trans
      change ((206946791775397 / 140737488355328 : ℚ) : ℝ) ≤ ((413893583550794 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (92 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height002.height_factor_upper_92.trans
      change ((3109771240984317 / 281474976710656 : ℚ) : ℝ) ≤ ((3109771240984317 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height002.height_power_upper_92.trans
      change ((418437208020515 / 281474976710656 : ℚ) : ℝ) ≤ ((418437208020515 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (93 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height002.height_factor_upper_93.trans
      change ((3081260201342375 / 281474976710656 : ℚ) : ℝ) ≤ ((3081260201342375 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height002.height_power_upper_93.trans
      change ((422980757236699 / 281474976710656 : ℚ) : ℝ) ≤ ((422980757236699 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (94 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height002.height_factor_upper_94.trans
      change ((3053008654353867 / 281474976710656 : ℚ) : ℝ) ≤ ((3053008654353867 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height002.height_power_upper_94.trans
      change ((427524231277109 / 281474976710656 : ℚ) : ℝ) ≤ ((427524231277109 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (95 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height002.height_factor_upper_95.trans
      change ((378126782221541 / 35184372088832 : ℚ) : ℝ) ≤ ((3025014257772328 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height002.height_power_upper_95.trans
      change ((216033815109693 / 140737488355328 : ℚ) : ℝ) ≤ ((432067630219386 : ℕ) : ℝ) / 2^48
      norm_num
end LegendreK6.M2Pilot.FactorBounds.Height002
