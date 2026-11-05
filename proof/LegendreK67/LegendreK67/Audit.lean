/-
Copyright (c) 2026 AI4Math legendre_k67 project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AI4Math legendre_k67 project (drafted with Claude)
-/
import LegendreK67

/-! 公理审计：确认这些定理只依赖 Lean/Mathlib 的标准公理（propext、Classical.choice、Quot.sound），
没有 `sorry`，也没有自定义公理。主定理对解析输入的依赖都写在 `Hypotheses` 结构的字段里。 -/

#print axioms LegendreK67.primes_between_consecutive_powers
#print axioms LegendreK67.main_of_gap
#print axioms LegendreK67.key_ineq
#print axioms LegendreK67.binom_lower
#print axioms LegendreK67.exists_prime_of_theta_sub_pos
#print axioms LegendreK67.abel_bound
#print axioms LegendreK67.propH_combination
#print axioms LegendreK67.propS_combination
#print axioms LegendreK67.integral_exp_bound
#print axioms LegendreK67.ineq32_of_CHL
#print axioms LegendreK67.theta_sub_pos_of_prime
#print axioms LegendreK67.main_k70
#print axioms LegendreK67.main_k74
#print axioms LegendreK67.ineq32_of_CHL_range
