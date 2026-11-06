import LegendreK6.M3Far.Enclosures.Sigma005
import LegendreK6.M3FarIntegerData

/-! Join checked analytic enclosures to the exact dyadic witness table. -/
namespace LegendreK6.M3Far.FactorBounds.Sigma005
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem bounds (i : Fin 384) (hlo : 160 ≤ i.val) (hhi : i.val < 192) :
    sigmaFactor i ≤ sigmaDyadicFactor i ∧ sigmaPower i ≤ sigmaDyadicPower i := by
  interval_cases hi : i.val
  · have heq : i = (160 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_160.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_160.trans
      change ((30547671891079 / 70368744177664 : ℚ) : ℝ) ≤ ((122190687564316 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (161 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_161.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_161.trans
      change ((121733662654985 / 281474976710656 : ℚ) : ℝ) ≤ ((121733662654985 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (162 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_162.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_162.trans
      change ((121275972498333 / 281474976710656 : ℚ) : ℝ) ≤ ((121275972498333 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (163 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_163.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_163.trans
      change ((120817615640797 / 281474976710656 : ℚ) : ℝ) ≤ ((120817615640797 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (164 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_164.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_164.trans
      change ((1880602978509 / 4398046511104 : ℚ) : ℝ) ≤ ((120358590624576 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (165 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_165.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_165.trans
      change ((59949447993809 / 140737488355328 : ℚ) : ℝ) ≤ ((119898895987618 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (166 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_166.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_166.trans
      change ((59719265131799 / 140737488355328 : ℚ) : ℝ) ≤ ((119438530263598 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (167 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_167.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_167.trans
      change ((118977491981909 / 281474976710656 : ℚ) : ℝ) ≤ ((118977491981909 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (168 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_168.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_168.trans
      change ((118515779667645 / 281474976710656 : ℚ) : ℝ) ≤ ((118515779667645 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (169 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_169.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_169.trans
      change ((118053391841583 / 281474976710656 : ℚ) : ℝ) ≤ ((118053391841583 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (170 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_170.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_170.trans
      change ((117590327020167 / 281474976710656 : ℚ) : ℝ) ≤ ((117590327020167 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (171 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_171.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_171.trans
      change ((117126583715497 / 281474976710656 : ℚ) : ℝ) ≤ ((117126583715497 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (172 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_172.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_172.trans
      change ((116662160435307 / 281474976710656 : ℚ) : ℝ) ≤ ((116662160435307 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (173 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_173.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_173.trans
      change ((14524631960369 / 35184372088832 : ℚ) : ℝ) ≤ ((116197055682952 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (174 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_174.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_174.trans
      change ((7233204247337 / 17592186044416 : ℚ) : ℝ) ≤ ((115731267957392 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (175 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_175.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_175.trans
      change ((14408099469147 / 35184372088832 : ℚ) : ℝ) ≤ ((115264795753176 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (176 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_176.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_176.trans
      change ((114797637560425 / 281474976710656 : ℚ) : ℝ) ≤ ((114797637560425 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (177 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_177.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_177.trans
      change ((57164895932407 / 140737488355328 : ℚ) : ℝ) ≤ ((114329791864814 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (178 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_178.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_178.trans
      change ((113861257147561 / 281474976710656 : ℚ) : ℝ) ≤ ((113861257147561 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (179 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_179.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_179.trans
      change ((28348007971351 / 70368744177664 : ℚ) : ℝ) ≤ ((113392031885404 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (180 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_180.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_180.trans
      change ((28230528637647 / 70368744177664 : ℚ) : ℝ) ≤ ((112922114550588 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (181 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_181.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_181.trans
      change ((112451503610851 / 281474976710656 : ℚ) : ℝ) ≤ ((112451503610851 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (182 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_182.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_182.trans
      change ((13997524691175 / 35184372088832 : ℚ) : ℝ) ≤ ((111980197529400 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (183 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_183.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_183.trans
      change ((55754097382451 / 140737488355328 : ℚ) : ℝ) ≤ ((111508194764902 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (184 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_184.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_184.trans
      change ((55517746885731 / 140737488355328 : ℚ) : ℝ) ≤ ((111035493771462 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (185 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_185.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_185.trans
      change ((55281046499305 / 140737488355328 : ℚ) : ℝ) ≤ ((110562092998610 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (186 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_186.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_186.trans
      change ((110087990891279 / 281474976710656 : ℚ) : ℝ) ≤ ((110087990891279 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (187 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_187.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_187.trans
      change ((54806592944897 / 140737488355328 : ℚ) : ℝ) ≤ ((109613185889794 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (188 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_188.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_188.trans
      change ((109137676429849 / 281474976710656 : ℚ) : ℝ) ≤ ((109137676429849 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (189 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_189.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_189.trans
      change ((3395670654453 / 8796093022208 : ℚ) : ℝ) ≤ ((108661460942496 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (190 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_190.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_190.trans
      change ((108184537854121 / 281474976710656 : ℚ) : ℝ) ≤ ((108184537854121 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (191 : Fin 384) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma005.sigma_factor_upper_191.trans
      change ((1 / 281474976710656 : ℚ) : ℝ) ≤ ((1 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma005.sigma_power_upper_191.trans
      change ((420730099947 / 1099511627776 : ℚ) : ℝ) ≤ ((107706905586432 : ℕ) : ℝ) / 2^48
      norm_num
end LegendreK6.M3Far.FactorBounds.Sigma005
