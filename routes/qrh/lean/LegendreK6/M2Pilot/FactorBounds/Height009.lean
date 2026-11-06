import LegendreK6.M2Pilot.Enclosures.Height009
import LegendreK6.M2PilotIntegerData

/-! Join checked analytic enclosures to the exact dyadic witness table. -/
namespace LegendreK6.M2Pilot.FactorBounds.Height009
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem bounds (i : Fin 988) (hlo : 288 ≤ i.val) (hhi : i.val < 320) :
    heightFactor i ≤ heightDyadicFactor i ∧ heightPower i ≤ heightDyadicPower i := by
  interval_cases hi : i.val
  · have heq : i = (288 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height009.height_factor_upper_288.trans
      change ((345874255267161 / 281474976710656 : ℚ) : ℝ) ≤ ((345874255267161 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height009.height_power_upper_288.trans
      change ((653812774593237 / 140737488355328 : ℚ) : ℝ) ≤ ((1307625549186474 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (289 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height009.height_factor_upper_289.trans
      change ((168676325077749 / 140737488355328 : ℚ) : ℝ) ≤ ((337352650155498 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height009.height_power_upper_289.trans
      change ((656077856281523 / 140737488355328 : ℚ) : ℝ) ≤ ((1312155712563046 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (290 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height009.height_factor_upper_290.trans
      change ((164520415089855 / 140737488355328 : ℚ) : ℝ) ≤ ((329040830179710 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height009.height_power_upper_290.trans
      change ((1316685813956567 / 281474976710656 : ℚ) : ℝ) ≤ ((1316685813956567 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (291 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height009.height_factor_upper_291.trans
      change ((160466817583307 / 140737488355328 : ℚ) : ℝ) ≤ ((320933635166614 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height009.height_power_upper_291.trans
      change ((1321215853425171 / 281474976710656 : ℚ) : ℝ) ≤ ((1321215853425171 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (292 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height009.height_factor_upper_292.trans
      change ((156513015879705 / 140737488355328 : ℚ) : ℝ) ≤ ((313026031759410 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height009.height_power_upper_292.trans
      change ((331436457756727 / 70368744177664 : ℚ) : ℝ) ≤ ((1325745831026908 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (293 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height009.height_factor_upper_293.trans
      change ((152656555151931 / 140737488355328 : ℚ) : ℝ) ≤ ((305313110303862 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height009.height_power_upper_293.trans
      change ((1330275746819745 / 281474976710656 : ℚ) : ℝ) ≤ ((1330275746819745 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (294 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height009.height_factor_upper_294.trans
      change ((297790081810879 / 281474976710656 : ℚ) : ℝ) ≤ ((297790081810879 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height009.height_power_upper_294.trans
      change ((1334805600861569 / 281474976710656 : ℚ) : ℝ) ≤ ((1334805600861569 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (295 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height009.height_factor_upper_295.trans
      change ((36306534374199 / 35184372088832 : ℚ) : ℝ) ≤ ((290452274993592 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height009.height_power_upper_295.trans
      change ((334833848302547 / 70368744177664 : ℚ) : ℝ) ≤ ((1339335393210188 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (296 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height009.height_factor_upper_296.trans
      change ((70823783344281 / 70368744177664 : ℚ) : ℝ) ≤ ((283295133377124 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height009.height_power_upper_296.trans
      change ((335966280980831 / 70368744177664 : ℚ) : ℝ) ≤ ((1343865123923324 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (297 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height009.height_factor_upper_297.trans
      change ((69078553119817 / 70368744177664 : ℚ) : ℝ) ≤ ((276314212479268 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height009.height_power_upper_297.trans
      change ((1348394793058623 / 281474976710656 : ℚ) : ℝ) ≤ ((1348394793058623 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (298 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height009.height_factor_upper_298.trans
      change ((8422036783135 / 8796093022208 : ℚ) : ℝ) ≤ ((269505177060320 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height009.height_power_upper_298.trans
      change ((676462200336823 / 140737488355328 : ℚ) : ℝ) ≤ ((1352924400673646 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (299 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height009.height_factor_upper_299.trans
      change ((262863798440393 / 281474976710656 : ℚ) : ℝ) ≤ ((262863798440393 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height009.height_power_upper_299.trans
      change ((339363486706469 / 70368744177664 : ℚ) : ℝ) ≤ ((1357453946825876 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (300 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height009.height_factor_upper_300.trans
      change ((256385951882545 / 281474976710656 : ℚ) : ℝ) ≤ ((256385951882545 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height009.height_power_upper_300.trans
      change ((680991715786357 / 140737488355328 : ℚ) : ℝ) ≤ ((1361983431572714 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (301 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height009.height_factor_upper_301.trans
      change ((250067614040111 / 281474976710656 : ℚ) : ℝ) ≤ ((250067614040111 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height009.height_power_upper_301.trans
      change ((683256427485741 / 140737488355328 : ℚ) : ℝ) ≤ ((1366512854971482 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (302 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height009.height_factor_upper_302.trans
      change ((121952430233331 / 140737488355328 : ℚ) : ℝ) ≤ ((243904860466662 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height009.height_power_upper_302.trans
      change ((1371042217079421 / 281474976710656 : ℚ) : ℝ) ≤ ((1371042217079421 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (303 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height009.height_factor_upper_303.trans
      change ((59473465796767 / 70368744177664 : ℚ) : ℝ) ≤ ((237893863187068 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height009.height_power_upper_303.trans
      change ((343892879488423 / 70368744177664 : ℚ) : ℝ) ≤ ((1375571517953692 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (304 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height009.height_factor_upper_304.trans
      change ((232030888328153 / 281474976710656 : ℚ) : ℝ) ≤ ((232030888328153 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height009.height_power_upper_304.trans
      change ((86256297353211 / 17592186044416 : ℚ) : ℝ) ≤ ((1380100757651376 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (305 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height009.height_factor_upper_305.trans
      change ((113156146903743 / 140737488355328 : ℚ) : ℝ) ≤ ((226312293807486 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height009.height_power_upper_305.trans
      change ((1384629936229473 / 281474976710656 : ℚ) : ℝ) ≤ ((1384629936229473 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (306 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height009.height_factor_upper_306.trans
      change ((220734527078885 / 281474976710656 : ℚ) : ℝ) ≤ ((220734527078885 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height009.height_power_upper_306.trans
      change ((694579526872453 / 140737488355328 : ℚ) : ℝ) ≤ ((1389159053744906 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (307 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height009.height_factor_upper_307.trans
      change ((107647061466623 / 140737488355328 : ℚ) : ℝ) ≤ ((215294122933246 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height009.height_power_upper_307.trans
      change ((1393688110254517 / 281474976710656 : ℚ) : ℝ) ≤ ((1393688110254517 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (308 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height009.height_factor_upper_308.trans
      change ((209987701353333 / 281474976710656 : ℚ) : ℝ) ≤ ((209987701353333 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height009.height_power_upper_308.trans
      change ((1398217105815069 / 281474976710656 : ℚ) : ℝ) ≤ ((1398217105815069 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (309 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height009.height_factor_upper_309.trans
      change ((51202991355303 / 70368744177664 : ℚ) : ℝ) ≤ ((204811965421212 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height009.height_power_upper_309.trans
      change ((350686510120811 / 70368744177664 : ℚ) : ℝ) ≤ ((1402746040483244 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (310 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height009.height_factor_upper_310.trans
      change ((99881849638519 / 140737488355328 : ℚ) : ℝ) ≤ ((199763699277038 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height009.height_power_upper_310.trans
      change ((1407274914315649 / 281474976710656 : ℚ) : ℝ) ≤ ((1407274914315649 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (311 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height009.height_factor_upper_311.trans
      change ((194839766127933 / 281474976710656 : ℚ) : ℝ) ≤ ((194839766127933 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height009.height_power_upper_311.trans
      change ((176475465921101 / 35184372088832 : ℚ) : ℝ) ≤ ((1411803727368808 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (312 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height009.height_factor_upper_312.trans
      change ((190037106305727 / 281474976710656 : ℚ) : ℝ) ≤ ((190037106305727 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height009.height_power_upper_312.trans
      change ((44260389990599 / 8796093022208 : ℚ) : ℝ) ≤ ((1416332479699168 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (313 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height009.height_factor_upper_313.trans
      change ((185352735372373 / 281474976710656 : ℚ) : ℝ) ≤ ((185352735372373 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height009.height_power_upper_313.trans
      change ((710430585681549 / 140737488355328 : ℚ) : ℝ) ≤ ((1420861171363098 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (314 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height009.height_factor_upper_314.trans
      change ((90391871135927 / 140737488355328 : ℚ) : ℝ) ≤ ((180783742271854 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height009.height_power_upper_314.trans
      change ((178173725302111 / 35184372088832 : ℚ) : ℝ) ≤ ((1425389802416888 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (315 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height009.height_factor_upper_315.trans
      change ((176327287527445 / 281474976710656 : ℚ) : ℝ) ≤ ((176327287527445 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height009.height_power_upper_315.trans
      change ((1429918372916749 / 281474976710656 : ℚ) : ℝ) ≤ ((1429918372916749 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (316 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height009.height_factor_upper_316.trans
      change ((171980601483233 / 281474976710656 : ℚ) : ℝ) ≤ ((171980601483233 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height009.height_power_upper_316.trans
      change ((1434446882918815 / 281474976710656 : ℚ) : ℝ) ≤ ((1434446882918815 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (317 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height009.height_factor_upper_317.trans
      change ((167740982588781 / 281474976710656 : ℚ) : ℝ) ≤ ((167740982588781 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height009.height_power_upper_317.trans
      change ((359743833119785 / 70368744177664 : ℚ) : ℝ) ≤ ((1438975332479140 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (318 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height009.height_factor_upper_318.trans
      change ((20450724465739 / 35184372088832 : ℚ) : ℝ) ≤ ((163605795725912 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height009.height_power_upper_318.trans
      change ((180437965206713 / 35184372088832 : ℚ) : ℝ) ≤ ((1443503721653704 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (319 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height009.height_factor_upper_319.trans
      change ((39893117644137 / 70368744177664 : ℚ) : ℝ) ≤ ((159572470576548 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height009.height_power_upper_319.trans
      change ((1448032050498405 / 281474976710656 : ℚ) : ℝ) ≤ ((1448032050498405 : ℕ) : ℝ) / 2^48
      norm_num
end LegendreK6.M2Pilot.FactorBounds.Height009
