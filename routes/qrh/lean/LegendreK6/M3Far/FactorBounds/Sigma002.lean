import LegendreK6.M3Far.Enclosures.Sigma002
import LegendreK6.M3FarIntegerData

/-! Join checked analytic enclosures to the exact dyadic witness table. -/
namespace LegendreK6.M3Far.FactorBounds.Sigma002
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem bounds (i : Fin 384) (hlo : 64 ≤ i.val) (hhi : i.val < 96) :
    sigmaFactor i ≤ sigmaDyadicFactor i ∧ sigmaPower i ≤ sigmaDyadicPower i := by
  interval_cases hi : i.val
  · have heq : i = (64 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_64.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_64.trans
      change ((81586949771205 / 140737488355328 : ℚ) : ℝ) ≤ ((163173899542410 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (65 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_65.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_65.trans
      change ((40693640412735 / 70368744177664 : ℚ) : ℝ) ≤ ((162774561650940 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (66 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_66.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_66.trans
      change ((81187340221305 / 140737488355328 : ℚ) : ℝ) ≤ ((162374680442610 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (67 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_67.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_67.trans
      change ((161974254807857 / 281474976710656 : ℚ) : ℝ) ≤ ((161974254807857 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (68 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_68.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_68.trans
      change ((40393320908523 / 70368744177664 : ℚ) : ℝ) ≤ ((161573283634092 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (69 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_69.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_69.trans
      change ((161171765805693 / 281474976710656 : ℚ) : ℝ) ≤ ((161171765805693 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (70 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_70.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_70.trans
      change ((160769700203995 / 281474976710656 : ℚ) : ℝ) ≤ ((160769700203995 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (71 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_71.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_71.trans
      change ((80183542853639 / 140737488355328 : ℚ) : ℝ) ≤ ((160367085707278 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (72 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_72.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_72.trans
      change ((39990980297689 / 70368744177664 : ℚ) : ℝ) ≤ ((159963921190756 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (73 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_73.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_73.trans
      change ((79780102763285 / 140737488355328 : ℚ) : ℝ) ≤ ((159560205526570 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (74 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_74.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_74.trans
      change ((159155937583773 / 281474976710656 : ℚ) : ℝ) ≤ ((159155937583773 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (75 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_75.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_75.trans
      change ((39687779057081 / 70368744177664 : ℚ) : ℝ) ≤ ((158751116228324 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (76 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_76.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_76.trans
      change ((158345740323073 / 281474976710656 : ℚ) : ℝ) ≤ ((158345740323073 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (77 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_77.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_77.trans
      change ((157939808727753 / 281474976710656 : ℚ) : ℝ) ≤ ((157939808727753 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (78 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_78.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_78.trans
      change ((19691665037371 / 35184372088832 : ℚ) : ℝ) ≤ ((157533320298968 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (79 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_79.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_79.trans
      change ((78563136945093 / 140737488355328 : ℚ) : ℝ) ≤ ((157126273890186 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (80 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_80.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_80.trans
      change ((156718668351721 / 281474976710656 : ℚ) : ℝ) ≤ ((156718668351721 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (81 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_81.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_81.trans
      change ((156310502530729 / 281474976710656 : ℚ) : ℝ) ≤ ((156310502530729 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (82 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_82.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_82.trans
      change ((77950887635597 / 140737488355328 : ℚ) : ℝ) ≤ ((155901775271194 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (83 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_83.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_83.trans
      change ((38873121353479 / 70368744177664 : ℚ) : ℝ) ≤ ((155492485413916 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (84 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_84.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_84.trans
      change ((155082631796505 / 281474976710656 : ℚ) : ℝ) ≤ ((155082631796505 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (85 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_85.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_85.trans
      change ((38668053313341 / 70368744177664 : ℚ) : ℝ) ≤ ((154672213253364 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (86 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_86.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_86.trans
      change ((75322865535 / 137438953472 : ℚ) : ℝ) ≤ ((154261228615680 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (87 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_87.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_87.trans
      change ((153849676711415 / 281474976710656 : ℚ) : ℝ) ≤ ((153849676711415 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (88 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_88.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_88.trans
      change ((76718778182647 / 140737488355328 : ℚ) : ℝ) ≤ ((153437556365294 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (89 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_89.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_89.trans
      change ((153024866398791 / 281474976710656 : ℚ) : ℝ) ≤ ((153024866398791 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (90 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_90.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_90.trans
      change ((152611605630121 / 281474976710656 : ℚ) : ℝ) ≤ ((152611605630121 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (91 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_91.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_91.trans
      change ((38049443218557 / 70368744177664 : ℚ) : ℝ) ≤ ((152197772874228 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (92 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_92.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_92.trans
      change ((151783366942773 / 281474976710656 : ℚ) : ℝ) ≤ ((151783366942773 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (93 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_93.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_93.trans
      change ((151368386644123 / 281474976710656 : ℚ) : ℝ) ≤ ((151368386644123 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (94 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_94.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_94.trans
      change ((150952830783339 / 281474976710656 : ℚ) : ℝ) ≤ ((150952830783339 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (95 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma002.sigma_factor_upper_95.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma002.sigma_power_upper_95.trans
      change ((150536698162165 / 281474976710656 : ℚ) : ℝ) ≤ ((150536698162165 : ℕ) : ℝ) / 2^48
      norm_num
end LegendreK6.M3Far.FactorBounds.Sigma002
