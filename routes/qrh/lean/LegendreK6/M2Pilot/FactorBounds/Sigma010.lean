import LegendreK6.M2Pilot.Enclosures.Sigma010
import LegendreK6.M2PilotIntegerData

/-! Join checked analytic enclosures to the exact dyadic witness table. -/
namespace LegendreK6.M2Pilot.FactorBounds.Sigma010
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem bounds (i : Fin 1536) (hlo : 1280 ≤ i.val) (hhi : i.val < 1408) :
    sigmaFactor i ≤ sigmaDyadicFactor i ∧ sigmaPower i ≤ sigmaDyadicPower i := by
  interval_cases hi : i.val
  · have heq : i = (1280 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1280.trans
      change ((2759861 / 281474976710656 : ℚ) : ℝ) ≤ ((2759861 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1280.trans
      change ((39505259889215 / 281474976710656 : ℚ) : ℝ) ≤ ((39505259889215 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1281 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1281.trans
      change ((2835231 / 281474976710656 : ℚ) : ℝ) ≤ ((2835231 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1281.trans
      change ((39359034374511 / 281474976710656 : ℚ) : ℝ) ≤ ((39359034374511 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1282 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1282.trans
      change ((22755 / 2199023255552 : ℚ) : ℝ) ≤ ((2912640 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1282.trans
      change ((9803187177363 / 70368744177664 : ℚ) : ℝ) ≤ ((39212748709452 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1283 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1283.trans
      change ((2992141 / 281474976710656 : ℚ) : ℝ) ≤ ((2992141 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1283.trans
      change ((19533201428457 / 140737488355328 : ℚ) : ℝ) ≤ ((39066402856914 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1284 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1284.trans
      change ((12007 / 1099511627776 : ℚ) : ℝ) ≤ ((3073792 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1284.trans
      change ((19459998389873 / 140737488355328 : ℚ) : ℝ) ≤ ((38919996779746 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1285 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1285.trans
      change ((197353 / 17592186044416 : ℚ) : ℝ) ≤ ((3157648 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1285.trans
      change ((38773530440763 / 281474976710656 : ℚ) : ℝ) ≤ ((38773530440763 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1286 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1286.trans
      change ((1621885 / 140737488355328 : ℚ) : ℝ) ≤ ((3243770 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1286.trans
      change ((38627003802753 / 281474976710656 : ℚ) : ℝ) ≤ ((38627003802753 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1287 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1287.trans
      change ((1666109 / 140737488355328 : ℚ) : ℝ) ≤ ((3332218 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1287.trans
      change ((19240208414235 / 140737488355328 : ℚ) : ℝ) ≤ ((38480416828470 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1288 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1288.trans
      change ((1711527 / 140737488355328 : ℚ) : ℝ) ≤ ((3423054 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1288.trans
      change ((38333769480639 / 281474976710656 : ℚ) : ℝ) ≤ ((38333769480639 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1289 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1289.trans
      change ((1758171 / 140737488355328 : ℚ) : ℝ) ≤ ((3516342 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1289.trans
      change ((19093530860977 / 140737488355328 : ℚ) : ℝ) ≤ ((38187061721954 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1290 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1290.trans
      change ((3612147 / 281474976710656 : ℚ) : ℝ) ≤ ((3612147 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1290.trans
      change ((38040293515079 / 281474976710656 : ℚ) : ℝ) ≤ ((38040293515079 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1291 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1291.trans
      change ((3710537 / 281474976710656 : ℚ) : ℝ) ≤ ((3710537 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1291.trans
      change ((37893464822645 / 281474976710656 : ℚ) : ℝ) ≤ ((37893464822645 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1292 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1292.trans
      change ((3811581 / 281474976710656 : ℚ) : ℝ) ≤ ((3811581 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1292.trans
      change ((37746575607255 / 281474976710656 : ℚ) : ℝ) ≤ ((37746575607255 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1293 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1293.trans
      change ((3915349 / 281474976710656 : ℚ) : ℝ) ≤ ((3915349 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1293.trans
      change ((4699953228935 / 35184372088832 : ℚ) : ℝ) ≤ ((37599625831480 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1294 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1294.trans
      change ((4021915 / 281474976710656 : ℚ) : ℝ) ≤ ((4021915 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1294.trans
      change ((18726307728929 / 140737488355328 : ℚ) : ℝ) ≤ ((37452615457858 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1295 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1295.trans
      change ((516419 / 35184372088832 : ℚ) : ℝ) ≤ ((4131352 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1295.trans
      change ((9326386112225 / 70368744177664 : ℚ) : ℝ) ≤ ((37305544448900 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1296 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1296.trans
      change ((2121869 / 140737488355328 : ℚ) : ℝ) ≤ ((4243738 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1296.trans
      change ((9289603191771 / 70368744177664 : ℚ) : ℝ) ≤ ((37158412767084 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1297 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1297.trans
      change ((2179575 / 140737488355328 : ℚ) : ℝ) ≤ ((4359150 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1297.trans
      change ((4626402546857 / 35184372088832 : ℚ) : ℝ) ≤ ((37011220374856 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1298 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1298.trans
      change ((4477671 / 281474976710656 : ℚ) : ℝ) ≤ ((4477671 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1298.trans
      change ((36863967234633 / 281474976710656 : ℚ) : ℝ) ≤ ((36863967234633 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1299 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1299.trans
      change ((2299691 / 140737488355328 : ℚ) : ℝ) ≤ ((4599382 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1299.trans
      change ((286848853975 / 2199023255552 : ℚ) : ℝ) ≤ ((36716653308800 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1300 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1300.trans
      change ((295273 / 17592186044416 : ℚ) : ℝ) ≤ ((4724368 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1300.trans
      change ((36569278559711 / 281474976710656 : ℚ) : ℝ) ≤ ((36569278559711 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1301 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1301.trans
      change ((4852717 / 281474976710656 : ℚ) : ℝ) ≤ ((4852717 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1301.trans
      change ((18210921474845 / 140737488355328 : ℚ) : ℝ) ≤ ((36421842949690 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1302 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1302.trans
      change ((4984519 / 281474976710656 : ℚ) : ℝ) ≤ ((4984519 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1302.trans
      change ((36274346441027 / 281474976710656 : ℚ) : ℝ) ≤ ((36274346441027 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1303 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1303.trans
      change ((639983 / 35184372088832 : ℚ) : ℝ) ≤ ((5119864 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1303.trans
      change ((2257924312249 / 17592186044416 : ℚ) : ℝ) ≤ ((36126788995984 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1304 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1304.trans
      change ((164339 / 8796093022208 : ℚ) : ℝ) ≤ ((5258848 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1304.trans
      change ((17989585288395 / 140737488355328 : ℚ) : ℝ) ≤ ((35979170576790 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1305 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1305.trans
      change ((5401567 / 281474976710656 : ℚ) : ℝ) ≤ ((5401567 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1305.trans
      change ((35831491145643 / 281474976710656 : ℚ) : ℝ) ≤ ((35831491145643 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1306 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1306.trans
      change ((5548121 / 281474976710656 : ℚ) : ℝ) ≤ ((5548121 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1306.trans
      change ((35683750664711 / 281474976710656 : ℚ) : ℝ) ≤ ((35683750664711 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1307 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1307.trans
      change ((5698611 / 281474976710656 : ℚ) : ℝ) ≤ ((5698611 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1307.trans
      change ((35535949096129 / 281474976710656 : ℚ) : ℝ) ≤ ((35535949096129 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1308 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1308.trans
      change ((5853143 / 281474976710656 : ℚ) : ℝ) ≤ ((5853143 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1308.trans
      change ((17694043201001 / 140737488355328 : ℚ) : ℝ) ≤ ((35388086402002 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1309 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1309.trans
      change ((6011823 / 281474976710656 : ℚ) : ℝ) ≤ ((6011823 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1309.trans
      change ((35240162544403 / 281474976710656 : ℚ) : ℝ) ≤ ((35240162544403 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1310 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1310.trans
      change ((6174761 / 281474976710656 : ℚ) : ℝ) ≤ ((6174761 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1310.trans
      change ((35092177485373 / 281474976710656 : ℚ) : ℝ) ≤ ((35092177485373 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1311 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1311.trans
      change ((792759 / 35184372088832 : ℚ) : ℝ) ≤ ((6342072 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1311.trans
      change ((17472065593461 / 140737488355328 : ℚ) : ℝ) ≤ ((34944131186922 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1312 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1312.trans
      change ((3256935 / 140737488355328 : ℚ) : ℝ) ≤ ((6513870 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1312.trans
      change ((34796023611031 / 281474976710656 : ℚ) : ℝ) ≤ ((34796023611031 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1313 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1313.trans
      change ((6690275 / 281474976710656 : ℚ) : ℝ) ≤ ((6690275 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1313.trans
      change ((34647854719645 / 281474976710656 : ℚ) : ℝ) ≤ ((34647854719645 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1314 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1314.trans
      change ((3435705 / 140737488355328 : ℚ) : ℝ) ≤ ((6871410 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1314.trans
      change ((34499624474681 / 281474976710656 : ℚ) : ℝ) ≤ ((34499624474681 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1315 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1315.trans
      change ((7057399 / 281474976710656 : ℚ) : ℝ) ≤ ((7057399 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1315.trans
      change ((4293916604753 / 35184372088832 : ℚ) : ℝ) ≤ ((34351332838024 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1316 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1316.trans
      change ((7248371 / 281474976710656 : ℚ) : ℝ) ≤ ((7248371 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1316.trans
      change ((34202979771525 / 281474976710656 : ℚ) : ℝ) ≤ ((34202979771525 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1317 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1317.trans
      change ((7444459 / 281474976710656 : ℚ) : ℝ) ≤ ((7444459 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1317.trans
      change ((34054565237005 / 281474976710656 : ℚ) : ℝ) ≤ ((34054565237005 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1318 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1318.trans
      change ((7645797 / 281474976710656 : ℚ) : ℝ) ≤ ((7645797 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1318.trans
      change ((1059565287383 / 8796093022208 : ℚ) : ℝ) ≤ ((33906089196256 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1319 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1319.trans
      change ((3926263 / 140737488355328 : ℚ) : ℝ) ≤ ((7852526 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1319.trans
      change ((33757551611033 / 281474976710656 : ℚ) : ℝ) ≤ ((33757551611033 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1320 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1320.trans
      change ((2016197 / 70368744177664 : ℚ) : ℝ) ≤ ((8064788 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1320.trans
      change ((4201119055383 / 35184372088832 : ℚ) : ℝ) ≤ ((33608952443064 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1321 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1321.trans
      change ((8282729 / 281474976710656 : ℚ) : ℝ) ≤ ((8282729 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1321.trans
      change ((16730145827021 / 140737488355328 : ℚ) : ℝ) ≤ ((33460291654042 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1322 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1322.trans
      change ((2126625 / 70368744177664 : ℚ) : ℝ) ≤ ((8506500 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1322.trans
      change ((16655784602815 / 140737488355328 : ℚ) : ℝ) ≤ ((33311569205630 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1323 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1323.trans
      change ((4368127 / 140737488355328 : ℚ) : ℝ) ≤ ((8736254 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1323.trans
      change ((8290696264865 / 70368744177664 : ℚ) : ℝ) ≤ ((33162785059460 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1324 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1324.trans
      change ((8972151 / 281474976710656 : ℚ) : ℝ) ≤ ((8972151 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1324.trans
      change ((33013939177129 / 281474976710656 : ℚ) : ℝ) ≤ ((33013939177129 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1325 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1325.trans
      change ((9214353 / 281474976710656 : ℚ) : ℝ) ≤ ((9214353 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1325.trans
      change ((8216257880051 / 70368744177664 : ℚ) : ℝ) ≤ ((32865031520204 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1326 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1326.trans
      change ((4731513 / 140737488355328 : ℚ) : ℝ) ≤ ((9463026 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1326.trans
      change ((16358031025111 / 140737488355328 : ℚ) : ℝ) ≤ ((32716062050222 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1327 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1327.trans
      change ((4859171 / 140737488355328 : ℚ) : ℝ) ≤ ((9718342 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1327.trans
      change ((32567030728685 / 281474976710656 : ℚ) : ℝ) ≤ ((32567030728685 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1328 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1328.trans
      change ((9980475 / 281474976710656 : ℚ) : ℝ) ≤ ((9980475 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1328.trans
      change ((4052242189633 / 35184372088832 : ℚ) : ℝ) ≤ ((32417937517064 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1329 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1329.trans
      change ((10249607 / 281474976710656 : ℚ) : ℝ) ≤ ((10249607 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1329.trans
      change ((16134391188399 / 140737488355328 : ℚ) : ℝ) ≤ ((32268782376798 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1330 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1330.trans
      change ((5262961 / 140737488355328 : ℚ) : ℝ) ≤ ((10525922 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1330.trans
      change ((2007472829331 / 17592186044416 : ℚ) : ℝ) ≤ ((32119565269296 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1331 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1331.trans
      change ((10809609 / 281474976710656 : ℚ) : ℝ) ≤ ((10809609 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1331.trans
      change ((31970286155931 / 281474976710656 : ℚ) : ℝ) ≤ ((31970286155931 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1332 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1332.trans
      change ((11100863 / 281474976710656 : ℚ) : ℝ) ≤ ((11100863 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1332.trans
      change ((15910472499023 / 140737488355328 : ℚ) : ℝ) ≤ ((31820944998046 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1333 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1333.trans
      change ((2849971 / 70368744177664 : ℚ) : ℝ) ≤ ((11399884 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1333.trans
      change ((15835770878477 / 140737488355328 : ℚ) : ℝ) ≤ ((31671541756954 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1334 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1334.trans
      change ((2926719 / 70368744177664 : ℚ) : ℝ) ≤ ((11706876 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1334.trans
      change ((31522076393931 / 281474976710656 : ℚ) : ℝ) ≤ ((31522076393931 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1335 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1335.trans
      change ((6011025 / 140737488355328 : ℚ) : ℝ) ≤ ((12022050 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1335.trans
      change ((31372548870225 / 281474976710656 : ℚ) : ℝ) ≤ ((31372548870225 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1336 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1336.trans
      change ((6172811 / 140737488355328 : ℚ) : ℝ) ≤ ((12345622 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1336.trans
      change ((31222959147051 / 281474976710656 : ℚ) : ℝ) ≤ ((31222959147051 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1337 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1337.trans
      change ((3169453 / 70368744177664 : ℚ) : ℝ) ≤ ((12677812 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1337.trans
      change ((7768326796397 / 70368744177664 : ℚ) : ℝ) ≤ ((31073307185588 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1338 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1338.trans
      change ((13018849 / 281474976710656 : ℚ) : ℝ) ≤ ((13018849 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1338.trans
      change ((30923592946989 / 281474976710656 : ℚ) : ℝ) ≤ ((30923592946989 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1339 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1339.trans
      change ((3342241 / 70368744177664 : ℚ) : ℝ) ≤ ((13368964 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1339.trans
      change ((30773816392369 / 281474976710656 : ℚ) : ℝ) ≤ ((30773816392369 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1340 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1340.trans
      change ((13728397 / 281474976710656 : ℚ) : ℝ) ≤ ((13728397 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1340.trans
      change ((15311988741407 / 140737488355328 : ℚ) : ℝ) ≤ ((30623977482814 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1341 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1341.trans
      change ((14097393 / 281474976710656 : ℚ) : ℝ) ≤ ((14097393 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1341.trans
      change ((1904629761211 / 17592186044416 : ℚ) : ℝ) ≤ ((30474076179376 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1342 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1342.trans
      change ((3619051 / 70368744177664 : ℚ) : ℝ) ≤ ((14476204 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1342.trans
      change ((30324112443075 / 281474976710656 : ℚ) : ℝ) ≤ ((30324112443075 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1343 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1343.trans
      change ((232267 / 4398046511104 : ℚ) : ℝ) ≤ ((14865088 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1343.trans
      change ((7543521558725 / 70368744177664 : ℚ) : ℝ) ≤ ((30174086234900 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1344 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1344.trans
      change ((7632155 / 140737488355328 : ℚ) : ℝ) ≤ ((15264310 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1344.trans
      change ((7505999378951 / 70368744177664 : ℚ) : ℝ) ≤ ((30023997515804 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1345 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1345.trans
      change ((7837071 / 140737488355328 : ℚ) : ℝ) ≤ ((15674142 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1345.trans
      change ((14936923123355 / 140737488355328 : ℚ) : ℝ) ≤ ((29873846246710 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1346 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1346.trans
      change ((8047431 / 140737488355328 : ℚ) : ℝ) ≤ ((16094862 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1346.trans
      change ((29723632388509 / 281474976710656 : ℚ) : ℝ) ≤ ((29723632388509 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1347 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1347.trans
      change ((4131689 / 70368744177664 : ℚ) : ℝ) ≤ ((16526756 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1347.trans
      change ((14786677951029 / 140737488355328 : ℚ) : ℝ) ≤ ((29573355902058 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1348 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1348.trans
      change ((16970119 / 281474976710656 : ℚ) : ℝ) ≤ ((16970119 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1348.trans
      change ((29423016748181 / 281474976710656 : ℚ) : ℝ) ≤ ((29423016748181 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1349 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1349.trans
      change ((4356313 / 70368744177664 : ℚ) : ℝ) ≤ ((17425252 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1349.trans
      change ((29272614887671 / 281474976710656 : ℚ) : ℝ) ≤ ((29272614887671 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1350 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1350.trans
      change ((8946231 / 140737488355328 : ℚ) : ℝ) ≤ ((17892462 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1350.trans
      change ((29122150281287 / 281474976710656 : ℚ) : ℝ) ≤ ((29122150281287 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1351 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1351.trans
      change ((4593017 / 70368744177664 : ℚ) : ℝ) ≤ ((18372068 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1351.trans
      change ((14485811444877 / 140737488355328 : ℚ) : ℝ) ≤ ((28971622889754 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1352 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1352.trans
      change ((9432197 / 140737488355328 : ℚ) : ℝ) ≤ ((18864394 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1352.trans
      change ((3602629084221 / 35184372088832 : ℚ) : ℝ) ≤ ((28821032673768 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1353 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1353.trans
      change ((19369775 / 281474976710656 : ℚ) : ℝ) ≤ ((19369775 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1353.trans
      change ((28670379593989 / 281474976710656 : ℚ) : ℝ) ≤ ((28670379593989 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1354 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1354.trans
      change ((19888551 / 281474976710656 : ℚ) : ℝ) ≤ ((19888551 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1354.trans
      change ((28519663611045 / 281474976710656 : ℚ) : ℝ) ≤ ((28519663611045 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1355 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1355.trans
      change ((20421075 / 281474976710656 : ℚ) : ℝ) ≤ ((20421075 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1355.trans
      change ((7092221171383 / 70368744177664 : ℚ) : ℝ) ≤ ((28368884685532 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1356 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1356.trans
      change ((20967707 / 281474976710656 : ℚ) : ℝ) ≤ ((20967707 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1356.trans
      change ((28218042778011 / 281474976710656 : ℚ) : ℝ) ≤ ((28218042778011 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1357 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1357.trans
      change ((21528817 / 281474976710656 : ℚ) : ℝ) ≤ ((21528817 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1357.trans
      change ((7016784462253 / 70368744177664 : ℚ) : ℝ) ≤ ((28067137849012 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1358 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1358.trans
      change ((22104783 / 281474976710656 : ℚ) : ℝ) ≤ ((22104783 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1358.trans
      change ((3489521232379 / 35184372088832 : ℚ) : ℝ) ≤ ((27916169859032 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1359 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1359.trans
      change ((11347997 / 140737488355328 : ℚ) : ℝ) ≤ ((22695994 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1359.trans
      change ((27765138768533 / 281474976710656 : ℚ) : ℝ) ≤ ((27765138768533 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1360 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1360.trans
      change ((11651425 / 140737488355328 : ℚ) : ℝ) ≤ ((23302850 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1360.trans
      change ((27614044537947 / 281474976710656 : ℚ) : ℝ) ≤ ((27614044537947 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1361 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1361.trans
      change ((23925759 / 281474976710656 : ℚ) : ℝ) ≤ ((23925759 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1361.trans
      change ((27462887127669 / 281474976710656 : ℚ) : ℝ) ≤ ((27462887127669 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1362 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1362.trans
      change ((12282571 / 140737488355328 : ℚ) : ℝ) ≤ ((24565142 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1362.trans
      change ((27311666498065 / 281474976710656 : ℚ) : ℝ) ≤ ((27311666498065 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1363 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1363.trans
      change ((12610715 / 140737488355328 : ℚ) : ℝ) ≤ ((25221430 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1363.trans
      change ((27160382609465 / 281474976710656 : ℚ) : ℝ) ≤ ((27160382609465 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1364 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1364.trans
      change ((3236883 / 35184372088832 : ℚ) : ℝ) ≤ ((25895064 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1364.trans
      change ((27009035422167 / 281474976710656 : ℚ) : ℝ) ≤ ((27009035422167 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1365 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1365.trans
      change ((26586497 / 281474976710656 : ℚ) : ℝ) ≤ ((26586497 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1365.trans
      change ((26857624896435 / 281474976710656 : ℚ) : ℝ) ≤ ((26857624896435 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1366 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1366.trans
      change ((6824049 / 70368744177664 : ℚ) : ℝ) ≤ ((27296196 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1366.trans
      change ((6676537748125 / 70368744177664 : ℚ) : ℝ) ≤ ((26706150992500 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1367 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1367.trans
      change ((7006159 / 70368744177664 : ℚ) : ℝ) ≤ ((28024636 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1367.trans
      change ((26554613670561 / 281474976710656 : ℚ) : ℝ) ≤ ((26554613670561 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1368 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1368.trans
      change ((28772307 / 281474976710656 : ℚ) : ℝ) ≤ ((28772307 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1368.trans
      change ((13201506445391 / 140737488355328 : ℚ) : ℝ) ≤ ((26403012890782 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1369 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1369.trans
      change ((29539711 / 281474976710656 : ℚ) : ℝ) ≤ ((29539711 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1369.trans
      change ((13125674306647 / 140737488355328 : ℚ) : ℝ) ≤ ((26251348613294 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1370 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1370.trans
      change ((30327363 / 281474976710656 : ℚ) : ℝ) ≤ ((30327363 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1370.trans
      change ((6524905199549 / 70368744177664 : ℚ) : ℝ) ≤ ((26099620798196 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1371 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1371.trans
      change ((31135791 / 281474976710656 : ℚ) : ℝ) ≤ ((31135791 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1371.trans
      change ((12973914702775 / 140737488355328 : ℚ) : ℝ) ≤ ((25947829405550 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1372 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1372.trans
      change ((998923 / 8796093022208 : ℚ) : ℝ) ≤ ((31965536 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1372.trans
      change ((25795974395389 / 281474976710656 : ℚ) : ℝ) ≤ ((25795974395389 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1373 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1373.trans
      change ((8204289 / 70368744177664 : ℚ) : ℝ) ≤ ((32817156 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1373.trans
      change ((25644055727709 / 281474976710656 : ℚ) : ℝ) ≤ ((25644055727709 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1374 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1374.trans
      change ((33691219 / 281474976710656 : ℚ) : ℝ) ≤ ((33691219 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1374.trans
      change ((25492073362475 / 281474976710656 : ℚ) : ℝ) ≤ ((25492073362475 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1375 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1375.trans
      change ((17294155 / 140737488355328 : ℚ) : ℝ) ≤ ((34588310 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1375.trans
      change ((791875851863 / 8796093022208 : ℚ) : ℝ) ≤ ((25340027259616 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1376 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1376.trans
      change ((35509029 / 281474976710656 : ℚ) : ℝ) ≤ ((35509029 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1376.trans
      change ((12593958689515 / 140737488355328 : ℚ) : ℝ) ≤ ((25187917379030 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1377 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1377.trans
      change ((4556749 / 35184372088832 : ℚ) : ℝ) ≤ ((36453992 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1377.trans
      change ((25035743680579 / 281474976710656 : ℚ) : ℝ) ≤ ((25035743680579 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1378 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1378.trans
      change ((37423829 / 281474976710656 : ℚ) : ℝ) ≤ ((37423829 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1378.trans
      change ((24883506124093 / 281474976710656 : ℚ) : ℝ) ≤ ((24883506124093 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1379 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1379.trans
      change ((9604797 / 70368744177664 : ℚ) : ℝ) ≤ ((38419188 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1379.trans
      change ((12365602334683 / 140737488355328 : ℚ) : ℝ) ≤ ((24731204669366 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1380 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1380.trans
      change ((9860183 / 70368744177664 : ℚ) : ℝ) ≤ ((39440732 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1380.trans
      change ((12289419638081 / 140737488355328 : ℚ) : ℝ) ≤ ((24578839276162 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1381 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1381.trans
      change ((40489143 / 281474976710656 : ℚ) : ℝ) ≤ ((40489143 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1381.trans
      change ((24426409904207 / 281474976710656 : ℚ) : ℝ) ≤ ((24426409904207 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1382 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1382.trans
      change ((41565119 / 281474976710656 : ℚ) : ℝ) ≤ ((41565119 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1382.trans
      change ((24273916513197 / 281474976710656 : ℚ) : ℝ) ≤ ((24273916513197 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1383 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1383.trans
      change ((666709 / 4398046511104 : ℚ) : ℝ) ≤ ((42669376 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1383.trans
      change ((24121359062791 / 281474976710656 : ℚ) : ℝ) ≤ ((24121359062791 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1384 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1384.trans
      change ((43802649 / 281474976710656 : ℚ) : ℝ) ≤ ((43802649 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1384.trans
      change ((23968737512617 / 281474976710656 : ℚ) : ℝ) ≤ ((23968737512617 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1385 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1385.trans
      change ((11241423 / 70368744177664 : ℚ) : ℝ) ≤ ((44965692 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1385.trans
      change ((23816051822265 / 281474976710656 : ℚ) : ℝ) ≤ ((23816051822265 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1386 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1386.trans
      change ((23079639 / 140737488355328 : ℚ) : ℝ) ≤ ((46159278 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1386.trans
      change ((369739092989 / 4398046511104 : ℚ) : ℝ) ≤ ((23663301951296 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1387 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1387.trans
      change ((47384199 / 281474976710656 : ℚ) : ℝ) ≤ ((47384199 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1387.trans
      change ((23510487859233 / 281474976710656 : ℚ) : ℝ) ≤ ((23510487859233 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1388 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1388.trans
      change ((12160317 / 70368744177664 : ℚ) : ℝ) ≤ ((48641268 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1388.trans
      change ((23357609505567 / 281474976710656 : ℚ) : ℝ) ≤ ((23357609505567 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1389 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1389.trans
      change ((49931321 / 281474976710656 : ℚ) : ℝ) ≤ ((49931321 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1389.trans
      change ((11602333424877 / 140737488355328 : ℚ) : ℝ) ≤ ((23204666849754 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1390 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1390.trans
      change ((51255211 / 281474976710656 : ℚ) : ℝ) ≤ ((51255211 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1390.trans
      change ((23051659851217 / 281474976710656 : ℚ) : ℝ) ≤ ((23051659851217 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1391 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1391.trans
      change ((6576727 / 35184372088832 : ℚ) : ℝ) ≤ ((52613816 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1391.trans
      change ((22898588469343 / 281474976710656 : ℚ) : ℝ) ≤ ((22898588469343 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1392 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1392.trans
      change ((13502009 / 70368744177664 : ℚ) : ℝ) ≤ ((54008036 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1392.trans
      change ((355397697867 / 4398046511104 : ℚ) : ℝ) ≤ ((22745452663488 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1393 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1393.trans
      change ((27719397 / 140737488355328 : ℚ) : ℝ) ≤ ((55438794 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1393.trans
      change ((11296126196485 / 140737488355328 : ℚ) : ℝ) ≤ ((22592252392970 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1394 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1394.trans
      change ((56907035 / 281474976710656 : ℚ) : ℝ) ≤ ((56907035 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1394.trans
      change ((22438987617075 / 281474976710656 : ℚ) : ℝ) ≤ ((22438987617075 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1395 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1395.trans
      change ((58413731 / 281474976710656 : ℚ) : ℝ) ≤ ((58413731 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1395.trans
      change ((22285658295053 / 281474976710656 : ℚ) : ℝ) ≤ ((22285658295053 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1396 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1396.trans
      change ((14989969 / 70368744177664 : ℚ) : ℝ) ≤ ((59959876 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1396.trans
      change ((22132264386123 / 281474976710656 : ℚ) : ℝ) ≤ ((22132264386123 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1397 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1397.trans
      change ((15386623 / 70368744177664 : ℚ) : ℝ) ≤ ((61546492 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1397.trans
      change ((21978805849467 / 281474976710656 : ℚ) : ℝ) ≤ ((21978805849467 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1398 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1398.trans
      change ((31587313 / 140737488355328 : ℚ) : ℝ) ≤ ((63174626 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1398.trans
      change ((2728160330529 / 35184372088832 : ℚ) : ℝ) ≤ ((21825282644232 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1399 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1399.trans
      change ((64845351 / 281474976710656 : ℚ) : ℝ) ≤ ((64845351 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1399.trans
      change ((5417923682383 / 70368744177664 : ℚ) : ℝ) ≤ ((21671694729532 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1400 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1400.trans
      change ((66559767 / 281474976710656 : ℚ) : ℝ) ≤ ((66559767 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1400.trans
      change ((10759021032223 / 140737488355328 : ℚ) : ℝ) ≤ ((21518042064446 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1401 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1401.trans
      change ((68319005 / 281474976710656 : ℚ) : ℝ) ≤ ((68319005 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1401.trans
      change ((5341081152005 / 70368744177664 : ℚ) : ℝ) ≤ ((21364324608020 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1402 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1402.trans
      change ((35062111 / 140737488355328 : ℚ) : ℝ) ≤ ((70124222 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1402.trans
      change ((21210542319263 / 281474976710656 : ℚ) : ℝ) ≤ ((21210542319263 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1403 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1403.trans
      change ((35988303 / 140737488355328 : ℚ) : ℝ) ≤ ((71976606 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1403.trans
      change ((10528347578575 / 140737488355328 : ℚ) : ℝ) ≤ ((21056695157150 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1404 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1404.trans
      change ((36938687 / 140737488355328 : ℚ) : ℝ) ≤ ((73877374 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1404.trans
      change ((20902783080623 / 281474976710656 : ℚ) : ℝ) ≤ ((20902783080623 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1405 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1405.trans
      change ((1184809 / 4398046511104 : ℚ) : ℝ) ≤ ((75827776 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1405.trans
      change ((5187201512147 / 70368744177664 : ℚ) : ℝ) ≤ ((20748806048588 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1406 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1406.trans
      change ((77829091 / 281474976710656 : ℚ) : ℝ) ≤ ((77829091 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1406.trans
      change ((5148691004979 / 70368744177664 : ℚ) : ℝ) ≤ ((20594764019916 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1407 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma010.sigma_factor_upper_1407.trans
      change ((39941317 / 140737488355328 : ℚ) : ℝ) ≤ ((79882634 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma010.sigma_power_upper_1407.trans
      change ((20440656953445 / 281474976710656 : ℚ) : ℝ) ≤ ((20440656953445 : ℕ) : ℝ) / 2^48
      norm_num
end LegendreK6.M2Pilot.FactorBounds.Sigma010
