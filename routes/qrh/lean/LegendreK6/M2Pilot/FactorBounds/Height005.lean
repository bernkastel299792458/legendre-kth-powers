import LegendreK6.M2Pilot.Enclosures.Height005
import LegendreK6.M2PilotIntegerData

/-! Join checked analytic enclosures to the exact dyadic witness table. -/
namespace LegendreK6.M2Pilot.FactorBounds.Height005
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem bounds (i : Fin 988) (hlo : 160 ≤ i.val) (hhi : i.val < 192) :
    heightFactor i ≤ heightDyadicFactor i ∧ heightPower i ≤ heightDyadicPower i := by
  interval_cases hi : i.val
  · have heq : i = (160 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height005.height_factor_upper_160.trans
      change ((207506133969103 / 35184372088832 : ℚ) : ℝ) ≤ ((1660049071752824 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height005.height_power_upper_160.trans
      change ((727231099970829 / 281474976710656 : ℚ) : ℝ) ≤ ((727231099970829 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (161 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height005.height_factor_upper_161.trans
      change ((1644762022765659 / 281474976710656 : ℚ) : ℝ) ≤ ((1644762022765659 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height005.height_power_upper_161.trans
      change ((731769708270977 / 281474976710656 : ℚ) : ℝ) ≤ ((731769708270977 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (162 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height005.height_factor_upper_162.trans
      change ((1629614801291187 / 281474976710656 : ℚ) : ℝ) ≤ ((1629614801291187 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height005.height_power_upper_162.trans
      change ((184077061603251 / 70368744177664 : ℚ) : ℝ) ≤ ((736308246413004 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (163 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height005.height_factor_upper_163.trans
      change ((1614606138080811 / 281474976710656 : ℚ) : ℝ) ≤ ((1614606138080811 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height005.height_power_upper_163.trans
      change ((740846714466911 / 281474976710656 : ℚ) : ℝ) ≤ ((740846714466911 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (164 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height005.height_factor_upper_164.trans
      change ((1599734775307365 / 281474976710656 : ℚ) : ℝ) ≤ ((1599734775307365 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height005.height_power_upper_164.trans
      change ((372692556251297 / 140737488355328 : ℚ) : ℝ) ≤ ((745385112502594 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (165 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height005.height_factor_upper_165.trans
      change ((792499733231681 / 140737488355328 : ℚ) : ℝ) ≤ ((1584999466463362 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height005.height_power_upper_165.trans
      change ((749923440589843 / 281474976710656 : ℚ) : ℝ) ≤ ((749923440589843 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (166 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height005.height_factor_upper_166.trans
      change ((1570398976260143 / 281474976710656 : ℚ) : ℝ) ≤ ((1570398976260143 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height005.height_power_upper_166.trans
      change ((188615424699587 / 70368744177664 : ℚ) : ℝ) ≤ ((754461698798348 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (167 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height005.height_factor_upper_167.trans
      change ((777966040263953 / 140737488355328 : ℚ) : ℝ) ≤ ((1555932080527906 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height005.height_power_upper_167.trans
      change ((758999887197689 / 281474976710656 : ℚ) : ℝ) ≤ ((758999887197689 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (168 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height005.height_factor_upper_168.trans
      change ((1541597566116623 / 281474976710656 : ℚ) : ℝ) ≤ ((1541597566116623 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height005.height_power_upper_168.trans
      change ((763538005857347 / 281474976710656 : ℚ) : ℝ) ≤ ((763538005857347 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (169 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height005.height_factor_upper_169.trans
      change ((763697115398913 / 140737488355328 : ℚ) : ℝ) ≤ ((1527394230797826 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height005.height_power_upper_169.trans
      change ((768076054846697 / 281474976710656 : ℚ) : ℝ) ≤ ((768076054846697 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (170 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height005.height_factor_upper_170.trans
      change ((1513320883167259 / 281474976710656 : ℚ) : ℝ) ≤ ((1513320883167259 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height005.height_power_upper_170.trans
      change ((772614034235011 / 281474976710656 : ℚ) : ℝ) ≤ ((772614034235011 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (171 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height005.height_factor_upper_171.trans
      change ((749688171274193 / 140737488355328 : ℚ) : ℝ) ≤ ((1499376342548386 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height005.height_power_upper_171.trans
      change ((388575972045729 / 140737488355328 : ℚ) : ℝ) ≤ ((777151944091458 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (172 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height005.height_factor_upper_172.trans
      change ((742779719448377 / 140737488355328 : ℚ) : ℝ) ≤ ((1485559438896754 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height005.height_power_upper_172.trans
      change ((781689784485103 / 281474976710656 : ℚ) : ℝ) ≤ ((781689784485103 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (173 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height005.height_factor_upper_173.trans
      change ((183983626588149 / 35184372088832 : ℚ) : ℝ) ≤ ((1471869012705192 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height005.height_power_upper_173.trans
      change ((786227555484909 / 281474976710656 : ℚ) : ℝ) ≤ ((786227555484909 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (174 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height005.height_factor_upper_174.trans
      change ((364575978727463 / 70368744177664 : ℚ) : ℝ) ≤ ((1458303914909852 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height005.height_power_upper_174.trans
      change ((790765257159737 / 281474976710656 : ℚ) : ℝ) ≤ ((790765257159737 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (175 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height005.height_factor_upper_175.trans
      change ((1444863006797073 / 281474976710656 : ℚ) : ℝ) ≤ ((1444863006797073 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height005.height_power_upper_175.trans
      change ((795302889578343 / 281474976710656 : ℚ) : ℝ) ≤ ((795302889578343 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (176 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height005.height_factor_upper_176.trans
      change ((715772579955535 / 140737488355328 : ℚ) : ℝ) ≤ ((1431545159911070 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height005.height_power_upper_176.trans
      change ((799840452809385 / 281474976710656 : ℚ) : ℝ) ≤ ((799840452809385 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (177 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height005.height_factor_upper_177.trans
      change ((1418349255962435 / 281474976710656 : ℚ) : ℝ) ≤ ((1418349255962435 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height005.height_power_upper_177.trans
      change ((402188973460707 / 140737488355328 : ℚ) : ℝ) ≤ ((804377946921414 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (178 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height005.height_factor_upper_178.trans
      change ((1405274186737445 / 281474976710656 : ℚ) : ℝ) ≤ ((1405274186737445 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height005.height_power_upper_178.trans
      change ((808915371982883 / 281474976710656 : ℚ) : ℝ) ≤ ((808915371982883 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (179 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height005.height_factor_upper_179.trans
      change ((696159427004085 / 140737488355328 : ℚ) : ℝ) ≤ ((1392318854008170 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height005.height_power_upper_179.trans
      change ((406726364031071 / 140737488355328 : ℚ) : ℝ) ≤ ((813452728062142 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (180 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height005.height_factor_upper_180.trans
      change ((689741084721687 / 140737488355328 : ℚ) : ℝ) ≤ ((1379482169443374 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height005.height_power_upper_180.trans
      change ((408995007613719 / 140737488355328 : ℚ) : ℝ) ≤ ((817990015227438 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (181 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height005.height_factor_upper_181.trans
      change ((1366763054520199 / 281474976710656 : ℚ) : ℝ) ≤ ((1366763054520199 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height005.height_power_upper_181.trans
      change ((822527233546921 / 281474976710656 : ℚ) : ℝ) ≤ ((822527233546921 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (182 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height005.height_factor_upper_182.trans
      change ((338540110109159 / 70368744177664 : ℚ) : ℝ) ≤ ((1354160440436636 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height005.height_power_upper_182.trans
      change ((827064383088635 / 281474976710656 : ℚ) : ℝ) ≤ ((827064383088635 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (183 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height005.height_factor_upper_183.trans
      change ((1341673268024759 / 281474976710656 : ℚ) : ℝ) ≤ ((1341673268024759 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height005.height_power_upper_183.trans
      change ((415800731960263 / 140737488355328 : ℚ) : ℝ) ≤ ((831601463920526 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (184 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height005.height_factor_upper_184.trans
      change ((1329300487664731 / 281474976710656 : ℚ) : ℝ) ≤ ((1329300487664731 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height005.height_power_upper_184.trans
      change ((836138476110439 / 281474976710656 : ℚ) : ℝ) ≤ ((836138476110439 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (185 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height005.height_factor_upper_185.trans
      change ((658520529599781 / 140737488355328 : ℚ) : ℝ) ≤ ((1317041059199562 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height005.height_power_upper_185.trans
      change ((420337709863059 / 140737488355328 : ℚ) : ℝ) ≤ ((840675419726118 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (186 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height005.height_factor_upper_186.trans
      change ((163111743981329 / 35184372088832 : ℚ) : ℝ) ≤ ((1304893951850632 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height005.height_power_upper_186.trans
      change ((845212294835209 / 281474976710656 : ℚ) : ℝ) ≤ ((845212294835209 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (187 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height005.height_factor_upper_187.trans
      change ((646429072066973 / 140737488355328 : ℚ) : ℝ) ≤ ((1292858144133946 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height005.height_power_upper_187.trans
      change ((849749101505253 / 281474976710656 : ℚ) : ℝ) ≤ ((849749101505253 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (188 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height005.height_factor_upper_188.trans
      change ((640466311888567 / 140737488355328 : ℚ) : ℝ) ≤ ((1280932623777134 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height005.height_power_upper_188.trans
      change ((854285839803697 / 281474976710656 : ℚ) : ℝ) ≤ ((854285839803697 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (189 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height005.height_factor_upper_189.trans
      change ((1269116387637187 / 281474976710656 : ℚ) : ℝ) ≤ ((1269116387637187 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height005.height_power_upper_189.trans
      change ((214705627449471 / 70368744177664 : ℚ) : ℝ) ≤ ((858822509797884 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (190 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height005.height_factor_upper_190.trans
      change ((628704220809457 / 140737488355328 : ℚ) : ℝ) ≤ ((1257408441618914 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height005.height_power_upper_190.trans
      change ((863359111555059 / 281474976710656 : ℚ) : ℝ) ≤ ((863359111555059 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (191 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height005.height_factor_upper_191.trans
      change ((622903900297061 / 140737488355328 : ℚ) : ℝ) ≤ ((1245807800594122 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height005.height_power_upper_191.trans
      change ((867895645142369 / 281474976710656 : ℚ) : ℝ) ≤ ((867895645142369 : ℕ) : ℝ) / 2^48
      norm_num
end LegendreK6.M2Pilot.FactorBounds.Height005
