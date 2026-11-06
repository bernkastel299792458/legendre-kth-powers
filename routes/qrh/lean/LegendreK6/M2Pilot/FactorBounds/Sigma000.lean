import LegendreK6.M2Pilot.Enclosures.Sigma000
import LegendreK6.M2PilotIntegerData

/-! Join checked analytic enclosures to the exact dyadic witness table. -/
namespace LegendreK6.M2Pilot.FactorBounds.Sigma000
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem bounds (i : Fin 1536) (hlo : 0 ≤ i.val) (hhi : i.val < 128) :
    sigmaFactor i ≤ sigmaDyadicFactor i ∧ sigmaPower i ≤ sigmaDyadicPower i := by
  interval_cases hi : i.val
  · have heq : i = (0 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_0.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_0.trans
      change ((187649984473771 / 281474976710656 : ℚ) : ℝ) ≤ ((187649984473771 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_1.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_1.trans
      change ((187558343589281 / 281474976710656 : ℚ) : ℝ) ≤ ((187558343589281 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (2 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_2.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_2.trans
      change ((187466672864061 / 281474976710656 : ℚ) : ℝ) ≤ ((187466672864061 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (3 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_3.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_3.trans
      change ((187374972283531 / 281474976710656 : ℚ) : ℝ) ≤ ((187374972283531 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (4 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_4.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_4.trans
      change ((93641620916553 / 140737488355328 : ℚ) : ℝ) ≤ ((187283241833106 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (5 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_5.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_5.trans
      change ((46797870374547 / 70368744177664 : ℚ) : ℝ) ≤ ((187191481498188 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (6 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_6.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_6.trans
      change ((187099691264171 / 281474976710656 : ℚ) : ℝ) ≤ ((187099691264171 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (7 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_7.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_7.trans
      change ((187007871116439 / 281474976710656 : ℚ) : ℝ) ≤ ((187007871116439 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (8 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_8.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_8.trans
      change ((186916021040367 / 281474976710656 : ℚ) : ℝ) ≤ ((186916021040367 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (9 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_9.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_9.trans
      change ((186824141021319 / 281474976710656 : ℚ) : ℝ) ≤ ((186824141021319 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (10 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_10.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_10.trans
      change ((186732231044653 / 281474976710656 : ℚ) : ℝ) ≤ ((186732231044653 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (11 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_11.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_11.trans
      change ((5832509096741 / 8796093022208 : ℚ) : ℝ) ≤ ((186640291095712 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (12 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_12.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_12.trans
      change ((186548321159835 / 281474976710656 : ℚ) : ℝ) ≤ ((186548321159835 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (13 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_13.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_13.trans
      change ((46614080305587 / 70368744177664 : ℚ) : ℝ) ≤ ((186456321222348 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (14 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_14.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_14.trans
      change ((23295536408571 / 35184372088832 : ℚ) : ℝ) ≤ ((186364291268568 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (15 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_15.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_15.trans
      change ((93136115641901 / 140737488355328 : ℚ) : ℝ) ≤ ((186272231283802 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (16 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_16.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_16.trans
      change ((93090070626675 / 140737488355328 : ℚ) : ℝ) ≤ ((186180141253350 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (17 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_17.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_17.trans
      change ((186088021162499 / 281474976710656 : ℚ) : ℝ) ≤ ((186088021162499 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (18 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_18.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_18.trans
      change ((185995870996529 / 281474976710656 : ℚ) : ℝ) ≤ ((185995870996529 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (19 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_19.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_19.trans
      change ((185903690740709 / 281474976710656 : ℚ) : ℝ) ≤ ((185903690740709 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (20 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_20.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_20.trans
      change ((185811480380299 / 281474976710656 : ℚ) : ℝ) ≤ ((185811480380299 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (21 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_21.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_21.trans
      change ((46429809975137 / 70368744177664 : ℚ) : ℝ) ≤ ((185719239900548 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (22 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_22.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_22.trans
      change ((185626969286697 / 281474976710656 : ℚ) : ℝ) ≤ ((185626969286697 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (23 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_23.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_23.trans
      change ((185534668523977 / 281474976710656 : ℚ) : ℝ) ≤ ((185534668523977 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (24 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_24.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_24.trans
      change ((185442337597609 / 281474976710656 : ℚ) : ℝ) ≤ ((185442337597609 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (25 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_25.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_25.trans
      change ((185349976492805 / 281474976710656 : ℚ) : ℝ) ≤ ((185349976492805 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (26 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_26.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_26.trans
      change ((92628792597383 / 140737488355328 : ℚ) : ℝ) ≤ ((185257585194766 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (27 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_27.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_27.trans
      change ((46291290922171 / 70368744177664 : ℚ) : ℝ) ≤ ((185165163688684 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (28 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_28.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_28.trans
      change ((185072711959743 / 281474976710656 : ℚ) : ℝ) ≤ ((185072711959743 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (29 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_29.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_29.trans
      change ((92490114996557 / 140737488355328 : ℚ) : ℝ) ≤ ((184980229993114 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (30 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_30.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_30.trans
      change ((184887717773961 / 281474976710656 : ℚ) : ℝ) ≤ ((184887717773961 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (31 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_31.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_31.trans
      change ((184795175287437 / 281474976710656 : ℚ) : ℝ) ≤ ((184795175287437 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (32 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_32.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_32.trans
      change ((92351301259343 / 140737488355328 : ℚ) : ℝ) ≤ ((184702602518686 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (33 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_33.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_33.trans
      change ((184609999452841 / 281474976710656 : ℚ) : ℝ) ≤ ((184609999452841 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (34 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_34.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_34.trans
      change ((184517366075027 / 281474976710656 : ℚ) : ℝ) ≤ ((184517366075027 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (35 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_35.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_35.trans
      change ((184424702370359 / 281474976710656 : ℚ) : ℝ) ≤ ((184424702370359 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (36 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_36.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_36.trans
      change ((46083002080985 / 70368744177664 : ℚ) : ℝ) ≤ ((184332008323940 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (37 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_37.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_37.trans
      change ((184239283920867 / 281474976710656 : ℚ) : ℝ) ≤ ((184239283920867 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (38 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_38.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_38.trans
      change ((184146529146223 / 281474976710656 : ℚ) : ℝ) ≤ ((184146529146223 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (39 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_39.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_39.trans
      change ((184053743985085 / 281474976710656 : ℚ) : ℝ) ≤ ((184053743985085 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (40 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_40.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_40.trans
      change ((183960928422517 / 281474976710656 : ℚ) : ℝ) ≤ ((183960928422517 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (41 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_41.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_41.trans
      change ((183868082443577 / 281474976710656 : ℚ) : ℝ) ≤ ((183868082443577 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (42 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_42.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_42.trans
      change ((91887603016655 / 140737488355328 : ℚ) : ℝ) ≤ ((183775206033310 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (43 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_43.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_43.trans
      change ((11480143698547 / 17592186044416 : ℚ) : ℝ) ≤ ((183682299176752 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (44 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_44.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_44.trans
      change ((183589361858929 / 281474976710656 : ℚ) : ℝ) ≤ ((183589361858929 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (45 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_45.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_45.trans
      change ((91748197032429 / 140737488355328 : ℚ) : ℝ) ≤ ((183496394064858 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (46 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_46.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_46.trans
      change ((183403395779547 / 281474976710656 : ℚ) : ℝ) ≤ ((183403395779547 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (47 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_47.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_47.trans
      change ((183310366987991 / 281474976710656 : ℚ) : ℝ) ≤ ((183310366987991 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (48 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_48.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_48.trans
      change ((91608653837589 / 140737488355328 : ℚ) : ℝ) ≤ ((183217307675178 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (49 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_49.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_49.trans
      change ((183124217826085 / 281474976710656 : ℚ) : ℝ) ≤ ((183124217826085 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (50 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_50.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_50.trans
      change ((11439443589105 / 17592186044416 : ℚ) : ℝ) ≤ ((183031097425680 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (51 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_51.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_51.trans
      change ((22867243307365 / 35184372088832 : ℚ) : ℝ) ≤ ((182937946458920 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (52 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_52.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_52.trans
      change ((182844764910753 / 281474976710656 : ℚ) : ℝ) ≤ ((182844764910753 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (53 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_53.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_53.trans
      change ((45687888191529 / 70368744177664 : ℚ) : ℝ) ≤ ((182751552766116 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (54 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_54.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_54.trans
      change ((182658310009937 / 281474976710656 : ℚ) : ℝ) ≤ ((182658310009937 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (55 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_55.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_55.trans
      change ((91282518313567 / 140737488355328 : ℚ) : ℝ) ≤ ((182565036627134 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (56 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_56.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_56.trans
      change ((22808966575327 / 35184372088832 : ℚ) : ℝ) ≤ ((182471732602616 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (57 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_57.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_57.trans
      change ((44525976055 / 68719476736 : ℚ) : ℝ) ≤ ((182378397921280 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (58 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_58.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_58.trans
      change ((91142516284007 / 140737488355328 : ℚ) : ℝ) ≤ ((182285032568014 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (59 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_59.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_59.trans
      change ((91095818263849 / 140737488355328 : ℚ) : ℝ) ≤ ((182191636527698 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (60 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_60.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_60.trans
      change ((91049104892599 / 140737488355328 : ℚ) : ℝ) ≤ ((182098209785198 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (61 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_61.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_61.trans
      change ((91002376162687 / 140737488355328 : ℚ) : ℝ) ≤ ((182004752325374 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (62 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_62.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_62.trans
      change ((90955632066537 / 140737488355328 : ℚ) : ℝ) ≤ ((181911264133074 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (63 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_63.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_63.trans
      change ((11363609074571 / 17592186044416 : ℚ) : ℝ) ≤ ((181817745193136 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (64 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_64.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_64.trans
      change ((181724195490389 / 281474976710656 : ℚ) : ℝ) ≤ ((181724195490389 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (65 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_65.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_65.trans
      change ((181630615009651 / 281474976710656 : ℚ) : ℝ) ≤ ((181630615009651 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (66 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_66.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_66.trans
      change ((181537003735731 / 281474976710656 : ℚ) : ℝ) ≤ ((181537003735731 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (67 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_67.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_67.trans
      change ((45360840413357 / 70368744177664 : ℚ) : ℝ) ≤ ((181443361653428 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (68 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_68.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_68.trans
      change ((181349688747529 / 281474976710656 : ℚ) : ℝ) ≤ ((181349688747529 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (69 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_69.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_69.trans
      change ((181255985002813 / 281474976710656 : ℚ) : ℝ) ≤ ((181255985002813 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (70 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_70.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_70.trans
      change ((181162250404049 / 281474976710656 : ℚ) : ℝ) ≤ ((181162250404049 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (71 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_71.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_71.trans
      change ((181068484935995 / 281474976710656 : ℚ) : ℝ) ≤ ((181068484935995 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (72 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_72.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_72.trans
      change ((22621836072925 / 35184372088832 : ℚ) : ℝ) ≤ ((180974688583400 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (73 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_73.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_73.trans
      change ((180880861331001 / 281474976710656 : ℚ) : ℝ) ≤ ((180880861331001 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (74 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_74.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_74.trans
      change ((22598375395441 / 35184372088832 : ℚ) : ℝ) ≤ ((180787003163528 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (75 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_75.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_75.trans
      change ((90346557032849 / 140737488355328 : ℚ) : ℝ) ≤ ((180693114065698 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (76 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_76.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_76.trans
      change ((180599194022219 / 281474976710656 : ℚ) : ℝ) ≤ ((180599194022219 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (77 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_77.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_77.trans
      change ((180505243017789 / 281474976710656 : ℚ) : ℝ) ≤ ((180505243017789 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (78 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_78.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_78.trans
      change ((90205630518549 / 140737488355328 : ℚ) : ℝ) ≤ ((180411261037098 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (79 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_79.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_79.trans
      change ((180317248064821 / 281474976710656 : ℚ) : ℝ) ≤ ((180317248064821 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (80 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_80.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_80.trans
      change ((180223204085627 / 281474976710656 : ℚ) : ℝ) ≤ ((180223204085627 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (81 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_81.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_81.trans
      change ((90064564542087 / 140737488355328 : ℚ) : ℝ) ≤ ((180129129084174 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (82 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_82.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_82.trans
      change ((180035023045109 / 281474976710656 : ℚ) : ℝ) ≤ ((180035023045109 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (83 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_83.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_83.trans
      change ((89970442976535 / 140737488355328 : ℚ) : ℝ) ≤ ((179940885953070 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (84 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_84.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_84.trans
      change ((44961679448171 / 70368744177664 : ℚ) : ℝ) ≤ ((179846717792684 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (85 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_85.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_85.trans
      change ((179752518548567 / 281474976710656 : ℚ) : ℝ) ≤ ((179752518548567 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (86 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_86.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_86.trans
      change ((179658288205327 / 281474976710656 : ℚ) : ℝ) ≤ ((179658288205327 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (87 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_87.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_87.trans
      change ((179564026747561 / 281474976710656 : ℚ) : ℝ) ≤ ((179564026747561 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (88 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_88.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_88.trans
      change ((179469734159855 / 281474976710656 : ℚ) : ℝ) ≤ ((179469734159855 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (89 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_89.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_89.trans
      change ((89687705213393 / 140737488355328 : ℚ) : ℝ) ≤ ((179375410426786 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (90 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_90.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_90.trans
      change ((179281055532919 / 281474976710656 : ℚ) : ℝ) ≤ ((179281055532919 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (91 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_91.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_91.trans
      change ((179186669462811 / 281474976710656 : ℚ) : ℝ) ≤ ((179186669462811 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (92 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_92.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_92.trans
      change ((11193265762563 / 17592186044416 : ℚ) : ℝ) ≤ ((179092252201008 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (93 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_93.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_93.trans
      change ((178997803732045 / 281474976710656 : ℚ) : ℝ) ≤ ((178997803732045 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (94 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_94.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_94.trans
      change ((698841109533 / 1099511627776 : ℚ) : ℝ) ≤ ((178903324040448 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (95 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_95.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_95.trans
      change ((44702203277683 / 70368744177664 : ℚ) : ℝ) ≤ ((178808813110732 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (96 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_96.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_96.trans
      change ((178714270927401 / 281474976710656 : ℚ) : ℝ) ≤ ((178714270927401 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (97 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_97.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_97.trans
      change ((178619697474951 / 281474976710656 : ℚ) : ℝ) ≤ ((178619697474951 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (98 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_98.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_98.trans
      change ((178525092737865 / 281474976710656 : ℚ) : ℝ) ≤ ((178525092737865 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (99 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_99.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_99.trans
      change ((89215228350309 / 140737488355328 : ℚ) : ℝ) ≤ ((178430456700618 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (100 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_100.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_100.trans
      change ((89167894673837 / 140737488355328 : ℚ) : ℝ) ≤ ((178335789347674 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (101 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_101.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_101.trans
      change ((89120545331743 / 140737488355328 : ℚ) : ℝ) ≤ ((178241090663486 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (102 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_102.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_102.trans
      change ((89073180316249 / 140737488355328 : ℚ) : ℝ) ≤ ((178146360632498 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (103 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_103.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_103.trans
      change ((89025799619571 / 140737488355328 : ℚ) : ℝ) ≤ ((178051599239142 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (104 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_104.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_104.trans
      change ((177956806467841 / 281474976710656 : ℚ) : ℝ) ≤ ((177956806467841 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (105 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_105.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_105.trans
      change ((5558186946969 / 8796093022208 : ℚ) : ℝ) ≤ ((177861982303008 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (106 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_106.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_106.trans
      change ((177767126729045 / 281474976710656 : ℚ) : ℝ) ≤ ((177767126729045 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (107 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_107.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_107.trans
      change ((88836119865171 / 140737488355328 : ℚ) : ℝ) ≤ ((177672239730342 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (108 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_108.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_108.trans
      change ((88788660645641 / 140737488355328 : ℚ) : ℝ) ≤ ((177577321291282 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (109 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_109.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_109.trans
      change ((44370592849059 / 70368744177664 : ℚ) : ℝ) ≤ ((177482371396236 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (110 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_110.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_110.trans
      change ((44346847507391 / 70368744177664 : ℚ) : ℝ) ≤ ((177387390029564 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (111 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_111.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_111.trans
      change ((177292377175617 / 281474976710656 : ℚ) : ℝ) ≤ ((177292377175617 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (112 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_112.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_112.trans
      change ((88598666409367 / 140737488355328 : ℚ) : ℝ) ≤ ((177197332818734 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (113 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_113.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_113.trans
      change ((44275564235811 / 70368744177664 : ℚ) : ℝ) ≤ ((177102256943244 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (114 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_114.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_114.trans
      change ((44251787383367 / 70368744177664 : ℚ) : ℝ) ≤ ((177007149533468 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (115 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_115.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_115.trans
      change ((176912010573713 / 281474976710656 : ℚ) : ℝ) ≤ ((176912010573713 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (116 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_116.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_116.trans
      change ((88408420024139 / 140737488355328 : ℚ) : ℝ) ≤ ((176816840048278 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (117 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_117.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_117.trans
      change ((176721637941451 / 281474976710656 : ℚ) : ℝ) ≤ ((176721637941451 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (118 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_118.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_118.trans
      change ((176626404237509 / 281474976710656 : ℚ) : ℝ) ≤ ((176626404237509 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (119 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_119.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_119.trans
      change ((11033196182545 / 17592186044416 : ℚ) : ℝ) ≤ ((176531138920720 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (120 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_120.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_120.trans
      change ((176435841975339 / 281474976710656 : ℚ) : ℝ) ≤ ((176435841975339 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (121 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_121.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_121.trans
      change ((176340513385613 / 281474976710656 : ℚ) : ℝ) ≤ ((176340513385613 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (122 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_122.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_122.trans
      change ((176245153135777 / 281474976710656 : ℚ) : ℝ) ≤ ((176245153135777 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (123 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_123.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_123.trans
      change ((176149761210057 / 281474976710656 : ℚ) : ℝ) ≤ ((176149761210057 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (124 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_124.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_124.trans
      change ((44013584398167 / 70368744177664 : ℚ) : ℝ) ≤ ((176054337592668 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (125 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_125.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_125.trans
      change ((175958882267813 / 281474976710656 : ℚ) : ℝ) ≤ ((175958882267813 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (126 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_126.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_126.trans
      change ((87931697609843 / 140737488355328 : ℚ) : ℝ) ≤ ((175863395219686 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (127 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma000.sigma_factor_upper_127.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma000.sigma_power_upper_127.trans
      change ((87883938216235 / 140737488355328 : ℚ) : ℝ) ≤ ((175767876432470 : ℕ) : ℝ) / 2^48
      norm_num
end LegendreK6.M2Pilot.FactorBounds.Sigma000
