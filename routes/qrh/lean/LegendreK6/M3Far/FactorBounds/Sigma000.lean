import LegendreK6.M3Far.Enclosures.Sigma000
import LegendreK6.M3FarIntegerData

/-! Join checked analytic enclosures to the exact dyadic witness table. -/
namespace LegendreK6.M3Far.FactorBounds.Sigma000
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem bounds (i : Fin 384) (hlo : 0 ≤ i.val) (hhi : i.val < 32) :
    sigmaFactor i ≤ sigmaDyadicFactor i ∧ sigmaPower i ≤ sigmaDyadicPower i := by
  interval_cases hi : i.val
  · have heq : i = (0 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_0.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_0.trans
      change ((187649984473771 / 281474976710656 : ℚ) : ℝ) ≤ ((187649984473771 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_1.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_1.trans
      change ((93641620916553 / 140737488355328 : ℚ) : ℝ) ≤ ((187283241833106 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (2 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_2.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_2.trans
      change ((186916021040367 / 281474976710656 : ℚ) : ℝ) ≤ ((186916021040367 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (3 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_3.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_3.trans
      change ((186548321159835 / 281474976710656 : ℚ) : ℝ) ≤ ((186548321159835 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (4 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_4.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_4.trans
      change ((93090070626675 / 140737488355328 : ℚ) : ℝ) ≤ ((186180141253350 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (5 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_5.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_5.trans
      change ((185811480380299 / 281474976710656 : ℚ) : ℝ) ≤ ((185811480380299 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (6 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_6.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_6.trans
      change ((185442337597609 / 281474976710656 : ℚ) : ℝ) ≤ ((185442337597609 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (7 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_7.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_7.trans
      change ((185072711959743 / 281474976710656 : ℚ) : ℝ) ≤ ((185072711959743 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (8 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_8.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_8.trans
      change ((92351301259343 / 140737488355328 : ℚ) : ℝ) ≤ ((184702602518686 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (9 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_9.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_9.trans
      change ((46083002080985 / 70368744177664 : ℚ) : ℝ) ≤ ((184332008323940 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (10 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_10.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_10.trans
      change ((183960928422517 / 281474976710656 : ℚ) : ℝ) ≤ ((183960928422517 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (11 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_11.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_11.trans
      change ((183589361858929 / 281474976710656 : ℚ) : ℝ) ≤ ((183589361858929 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (12 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_12.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_12.trans
      change ((91608653837589 / 140737488355328 : ℚ) : ℝ) ≤ ((183217307675178 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (13 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_13.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_13.trans
      change ((182844764910753 / 281474976710656 : ℚ) : ℝ) ≤ ((182844764910753 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (14 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_14.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_14.trans
      change ((22808966575327 / 35184372088832 : ℚ) : ℝ) ≤ ((182471732602616 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (15 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_15.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_15.trans
      change ((91049104892599 / 140737488355328 : ℚ) : ℝ) ≤ ((182098209785198 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (16 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_16.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_16.trans
      change ((181724195490389 / 281474976710656 : ℚ) : ℝ) ≤ ((181724195490389 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (17 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_17.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_17.trans
      change ((181349688747529 / 281474976710656 : ℚ) : ℝ) ≤ ((181349688747529 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (18 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_18.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_18.trans
      change ((22621836072925 / 35184372088832 : ℚ) : ℝ) ≤ ((180974688583400 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (19 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_19.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_19.trans
      change ((180599194022219 / 281474976710656 : ℚ) : ℝ) ≤ ((180599194022219 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (20 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_20.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_20.trans
      change ((180223204085627 / 281474976710656 : ℚ) : ℝ) ≤ ((180223204085627 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (21 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_21.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_21.trans
      change ((44961679448171 / 70368744177664 : ℚ) : ℝ) ≤ ((179846717792684 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (22 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_22.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_22.trans
      change ((179469734159855 / 281474976710656 : ℚ) : ℝ) ≤ ((179469734159855 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (23 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_23.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_23.trans
      change ((11193265762563 / 17592186044416 : ℚ) : ℝ) ≤ ((179092252201008 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (24 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_24.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_24.trans
      change ((178714270927401 / 281474976710656 : ℚ) : ℝ) ≤ ((178714270927401 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (25 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_25.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_25.trans
      change ((89167894673837 / 140737488355328 : ℚ) : ℝ) ≤ ((178335789347674 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (26 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_26.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_26.trans
      change ((177956806467841 / 281474976710656 : ℚ) : ℝ) ≤ ((177956806467841 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (27 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_27.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_27.trans
      change ((88788660645641 / 140737488355328 : ℚ) : ℝ) ≤ ((177577321291282 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (28 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_28.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_28.trans
      change ((88598666409367 / 140737488355328 : ℚ) : ℝ) ≤ ((177197332818734 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (29 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_29.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_29.trans
      change ((88408420024139 / 140737488355328 : ℚ) : ℝ) ≤ ((176816840048278 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (30 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_30.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_30.trans
      change ((176435841975339 / 281474976710656 : ℚ) : ℝ) ≤ ((176435841975339 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (31 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_31.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_31.trans
      change ((44013584398167 / 70368744177664 : ℚ) : ℝ) ≤ ((176054337592668 : ℕ) : ℝ) / 2^48
      norm_num
end LegendreK6.M3Far.FactorBounds.Sigma000
