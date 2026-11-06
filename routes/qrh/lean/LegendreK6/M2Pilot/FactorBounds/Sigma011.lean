import LegendreK6.M2Pilot.Enclosures.Sigma011
import LegendreK6.M2PilotIntegerData

/-! Join checked analytic enclosures to the exact dyadic witness table. -/
namespace LegendreK6.M2Pilot.FactorBounds.Sigma011
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem bounds (i : Fin 1536) (hlo : 1408 ≤ i.val) (hhi : i.val < 1536) :
    sigmaFactor i ≤ sigmaDyadicFactor i ∧ sigmaPower i ≤ sigmaDyadicPower i := by
  interval_cases hi : i.val
  · have heq : i = (1408 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1408.trans
      change ((46217423 / 140737488355328 : ℚ) : ℝ) ≤ ((92434846 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1408.trans
      change ((2535810600997 / 35184372088832 : ℚ) : ℝ) ≤ ((20286484807976 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1409 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1409.trans
      change ((23718089 / 70368744177664 : ℚ) : ℝ) ≤ ((94872356 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1409.trans
      change ((5033061885569 / 70368744177664 : ℚ) : ℝ) ≤ ((20132247542276 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1410 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1410.trans
      change ((48686709 / 140737488355328 : ℚ) : ℝ) ≤ ((97373418 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1410.trans
      change ((19977945115079 / 281474976710656 : ℚ) : ℝ) ≤ ((19977945115079 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1411 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1411.trans
      change ((49969835 / 140737488355328 : ℚ) : ℝ) ≤ ((99939670 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1411.trans
      change ((19823577485081 / 281474976710656 : ℚ) : ℝ) ≤ ((19823577485081 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1412 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1412.trans
      change ((102572791 / 281474976710656 : ℚ) : ℝ) ≤ ((102572791 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1412.trans
      change ((19669144610945 / 281474976710656 : ℚ) : ℝ) ≤ ((19669144610945 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1413 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1413.trans
      change ((52637251 / 140737488355328 : ℚ) : ℝ) ≤ ((105274502 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1413.trans
      change ((19514646451299 / 281474976710656 : ℚ) : ℝ) ≤ ((19514646451299 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1414 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1414.trans
      change ((108046569 / 281474976710656 : ℚ) : ℝ) ≤ ((108046569 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1414.trans
      change ((75625324081 / 1099511627776 : ℚ) : ℝ) ≤ ((19360082964736 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1415 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1415.trans
      change ((110890801 / 281474976710656 : ℚ) : ℝ) ≤ ((110890801 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1415.trans
      change ((19205454109813 / 281474976710656 : ℚ) : ℝ) ≤ ((19205454109813 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1416 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1416.trans
      change ((3556533 / 8796093022208 : ℚ) : ℝ) ≤ ((113809056 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1416.trans
      change ((19050759845053 / 281474976710656 : ℚ) : ℝ) ≤ ((19050759845053 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1417 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1417.trans
      change ((116803235 / 281474976710656 : ℚ) : ℝ) ≤ ((116803235 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1417.trans
      change ((1181000008059 / 17592186044416 : ℚ) : ℝ) ≤ ((18896000128944 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1418 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1418.trans
      change ((29968823 / 70368744177664 : ℚ) : ℝ) ≤ ((119875292 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1418.trans
      change ((18741174919937 / 281474976710656 : ℚ) : ℝ) ≤ ((18741174919937 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1419 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1419.trans
      change ((61513613 / 140737488355328 : ℚ) : ℝ) ≤ ((123027226 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1419.trans
      change ((9293142088225 / 140737488355328 : ℚ) : ℝ) ≤ ((18586284176450 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1420 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1420.trans
      change ((63130545 / 140737488355328 : ℚ) : ℝ) ≤ ((126261090 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1420.trans
      change ((18431327856865 / 281474976710656 : ℚ) : ℝ) ≤ ((18431327856865 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1421 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1421.trans
      change ((32394747 / 70368744177664 : ℚ) : ℝ) ≤ ((129578988 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1421.trans
      change ((18276305919529 / 281474976710656 : ℚ) : ℝ) ≤ ((18276305919529 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1422 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1422.trans
      change ((132983077 / 281474976710656 : ℚ) : ℝ) ≤ ((132983077 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1422.trans
      change ((18121218322753 / 281474976710656 : ℚ) : ℝ) ≤ ((18121218322753 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1423 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1423.trans
      change ((8529723 / 17592186044416 : ℚ) : ℝ) ≤ ((136475568 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1423.trans
      change ((8983032512407 / 140737488355328 : ℚ) : ℝ) ≤ ((17966065024814 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1424 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1424.trans
      change ((140058731 / 281474976710656 : ℚ) : ℝ) ≤ ((140058731 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1424.trans
      change ((1113177873997 / 17592186044416 : ℚ) : ℝ) ≤ ((17810845983952 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1425 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1425.trans
      change ((143734889 / 281474976710656 : ℚ) : ℝ) ≤ ((143734889 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1425.trans
      change ((4413890289593 / 70368744177664 : ℚ) : ℝ) ≤ ((17655561158372 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1426 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1426.trans
      change ((36876607 / 70368744177664 : ℚ) : ℝ) ≤ ((147506428 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1426.trans
      change ((4375052626561 / 70368744177664 : ℚ) : ℝ) ≤ ((17500210506244 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1427 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1427.trans
      change ((9460987 / 17592186044416 : ℚ) : ℝ) ≤ ((151375792 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1427.trans
      change ((2168099248213 / 35184372088832 : ℚ) : ℝ) ≤ ((17344793985704 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1428 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1428.trans
      change ((155345487 / 281474976710656 : ℚ) : ℝ) ≤ ((155345487 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1428.trans
      change ((8594655777425 / 140737488355328 : ℚ) : ℝ) ≤ ((17189311554850 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1429 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1429.trans
      change ((159418083 / 281474976710656 : ℚ) : ℝ) ≤ ((159418083 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1429.trans
      change ((17033763171745 / 281474976710656 : ℚ) : ℝ) ≤ ((17033763171745 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1430 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1430.trans
      change ((163596215 / 281474976710656 : ℚ) : ℝ) ≤ ((163596215 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1430.trans
      change ((16878148794417 / 281474976710656 : ℚ) : ℝ) ≤ ((16878148794417 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1431 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1431.trans
      change ((20985323 / 35184372088832 : ℚ) : ℝ) ≤ ((167882584 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1431.trans
      change ((8361234190429 / 140737488355328 : ℚ) : ℝ) ≤ ((16722468380858 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1432 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1432.trans
      change ((172279961 / 281474976710656 : ℚ) : ℝ) ≤ ((172279961 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1432.trans
      change ((8283360944513 / 140737488355328 : ℚ) : ℝ) ≤ ((16566721889026 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1433 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1433.trans
      change ((11049449 / 17592186044416 : ℚ) : ℝ) ≤ ((176791184 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1433.trans
      change ((16410909276841 / 281474976710656 : ℚ) : ℝ) ≤ ((16410909276841 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1434 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1434.trans
      change ((45354791 / 70368744177664 : ℚ) : ℝ) ≤ ((181419164 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1434.trans
      change ((16255030502187 / 281474976710656 : ℚ) : ℝ) ≤ ((16255030502187 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1435 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1435.trans
      change ((186166887 / 281474976710656 : ℚ) : ℝ) ≤ ((186166887 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1435.trans
      change ((16099085522915 / 281474976710656 : ℚ) : ℝ) ≤ ((16099085522915 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1436 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1436.trans
      change ((47759353 / 70368744177664 : ℚ) : ℝ) ≤ ((191037412 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1436.trans
      change ((15943074296837 / 281474976710656 : ℚ) : ℝ) ≤ ((15943074296837 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1437 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1437.trans
      change ((49008469 / 70368744177664 : ℚ) : ℝ) ≤ ((196033876 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1437.trans
      change ((15786996781733 / 281474976710656 : ℚ) : ℝ) ≤ ((15786996781733 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1438 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1438.trans
      change ((201159497 / 281474976710656 : ℚ) : ℝ) ≤ ((201159497 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1438.trans
      change ((7815426467671 / 140737488355328 : ℚ) : ℝ) ≤ ((15630852935342 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1439 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1439.trans
      change ((103208785 / 140737488355328 : ℚ) : ℝ) ≤ ((206417570 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1439.trans
      change ((3868660678843 / 70368744177664 : ℚ) : ℝ) ≤ ((15474642715372 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1440 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1440.trans
      change ((105905739 / 140737488355328 : ℚ) : ℝ) ≤ ((211811478 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1440.trans
      change ((3829591519873 / 70368744177664 : ℚ) : ℝ) ≤ ((15318366079492 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1441 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1441.trans
      change ((54336171 / 70368744177664 : ℚ) : ℝ) ≤ ((217344684 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1441.trans
      change ((1895252873167 / 35184372088832 : ℚ) : ℝ) ≤ ((15162022985336 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1442 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1442.trans
      change ((111510371 / 140737488355328 : ℚ) : ℝ) ≤ ((223020742 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1442.trans
      change ((7502806695251 / 140737488355328 : ℚ) : ℝ) ≤ ((15005613390502 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1443 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1443.trans
      change ((114421647 / 140737488355328 : ℚ) : ℝ) ≤ ((228843294 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1443.trans
      change ((1856142156569 / 35184372088832 : ℚ) : ℝ) ≤ ((14849137252552 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1444 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1444.trans
      change ((117408037 / 140737488355328 : ℚ) : ℝ) ≤ ((234816074 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1444.trans
      change ((14692594529011 / 281474976710656 : ℚ) : ℝ) ≤ ((14692594529011 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1445 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1445.trans
      change ((120471455 / 140737488355328 : ℚ) : ℝ) ≤ ((240942910 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1445.trans
      change ((14535985177369 / 281474976710656 : ℚ) : ℝ) ≤ ((14535985177369 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1446 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1446.trans
      change ((247227725 / 281474976710656 : ℚ) : ℝ) ≤ ((247227725 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1446.trans
      change ((14379309155079 / 281474976710656 : ℚ) : ℝ) ≤ ((14379309155079 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1447 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1447.trans
      change ((253674543 / 281474976710656 : ℚ) : ℝ) ≤ ((253674543 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1447.trans
      change ((7111283209779 / 140737488355328 : ℚ) : ℝ) ≤ ((14222566419558 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1448 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1448.trans
      change ((260287487 / 281474976710656 : ℚ) : ℝ) ≤ ((260287487 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1448.trans
      change ((3516439232047 / 70368744177664 : ℚ) : ℝ) ≤ ((14065756928188 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1449 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1449.trans
      change ((4172981 / 4398046511104 : ℚ) : ℝ) ≤ ((267070784 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1449.trans
      change ((1738610079789 / 35184372088832 : ℚ) : ℝ) ≤ ((13908880638312 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1450 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1450.trans
      change ((274028767 / 281474976710656 : ℚ) : ℝ) ≤ ((274028767 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1450.trans
      change ((13751937507239 / 281474976710656 : ℚ) : ℝ) ≤ ((13751937507239 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1451 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1451.trans
      change ((281165879 / 281474976710656 : ℚ) : ℝ) ≤ ((281165879 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1451.trans
      change ((849682968265 / 17592186044416 : ℚ) : ℝ) ≤ ((13594927492240 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1452 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1452.trans
      change ((144243337 / 140737488355328 : ℚ) : ℝ) ≤ ((288486674 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1452.trans
      change ((1679731318819 / 35184372088832 : ℚ) : ℝ) ≤ ((13437850550552 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1453 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1453.trans
      change ((147997909 / 140737488355328 : ℚ) : ℝ) ≤ ((295995818 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1453.trans
      change ((3320176659843 / 70368744177664 : ℚ) : ℝ) ≤ ((13280706639372 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1454 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1454.trans
      change ((303698097 / 281474976710656 : ℚ) : ℝ) ≤ ((303698097 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1454.trans
      change ((13123495715863 / 281474976710656 : ℚ) : ℝ) ≤ ((13123495715863 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1455 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1455.trans
      change ((19474901 / 17592186044416 : ℚ) : ℝ) ≤ ((311598416 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1455.trans
      change ((202597152143 / 4398046511104 : ℚ) : ℝ) ≤ ((12966217737152 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1456 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1456.trans
      change ((319701803 / 281474976710656 : ℚ) : ℝ) ≤ ((319701803 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1456.trans
      change ((6404436330163 / 140737488355328 : ℚ) : ℝ) ≤ ((12808872660326 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1457 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1457.trans
      change ((164006705 / 140737488355328 : ℚ) : ℝ) ≤ ((328013410 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1457.trans
      change ((12651460442439 / 281474976710656 : ℚ) : ℝ) ≤ ((12651460442439 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1458 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1458.trans
      change ((42067315 / 35184372088832 : ℚ) : ℝ) ≤ ((336538520 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1458.trans
      change ((3123495260127 / 70368744177664 : ℚ) : ℝ) ≤ ((12493981040508 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1459 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1459.trans
      change ((345282549 / 281474976710656 : ℚ) : ℝ) ≤ ((345282549 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1459.trans
      change ((6168217205755 / 140737488355328 : ℚ) : ℝ) ≤ ((12336434411510 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1460 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1460.trans
      change ((177125523 / 140737488355328 : ℚ) : ℝ) ≤ ((354251046 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1460.trans
      change ((12178820512389 / 281474976710656 : ℚ) : ℝ) ≤ ((12178820512389 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1461 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1461.trans
      change ((90862425 / 70368744177664 : ℚ) : ℝ) ≤ ((363449700 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1461.trans
      change ((6010569650025 / 140737488355328 : ℚ) : ℝ) ≤ ((12021139300050 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1462 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1462.trans
      change ((46610543 / 35184372088832 : ℚ) : ℝ) ≤ ((372884344 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1462.trans
      change ((5931695365681 / 140737488355328 : ℚ) : ℝ) ≤ ((11863390731362 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1463 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1463.trans
      change ((382560953 / 281474976710656 : ℚ) : ℝ) ≤ ((382560953 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1463.trans
      change ((5852787381579 / 140737488355328 : ℚ) : ℝ) ≤ ((11705574763158 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1464 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1464.trans
      change ((196242827 / 140737488355328 : ℚ) : ℝ) ≤ ((392485654 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1464.trans
      change ((11547691352233 / 281474976710656 : ℚ) : ℝ) ≤ ((11547691352233 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1465 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1465.trans
      change ((402664727 / 281474976710656 : ℚ) : ℝ) ≤ ((402664727 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1465.trans
      change ((711858778459 / 17592186044416 : ℚ) : ℝ) ≤ ((11389740455344 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1466 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1466.trans
      change ((12909519 / 8796093022208 : ℚ) : ℝ) ≤ ((413104608 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1466.trans
      change ((11231722029213 / 281474976710656 : ℚ) : ℝ) ≤ ((11231722029213 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1467 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1467.trans
      change ((423811893 / 281474976710656 : ℚ) : ℝ) ≤ ((423811893 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1467.trans
      change ((2768409007631 / 70368744177664 : ℚ) : ℝ) ≤ ((11073636030524 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1468 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1468.trans
      change ((3396823 / 2199023255552 : ℚ) : ℝ) ≤ ((434793344 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1468.trans
      change ((5457741207963 / 140737488355328 : ℚ) : ℝ) ≤ ((10915482415926 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1469 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1469.trans
      change ((446055891 / 281474976710656 : ℚ) : ℝ) ≤ ((446055891 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1469.trans
      change ((5378630571013 / 140737488355328 : ℚ) : ℝ) ≤ ((10757261142026 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1470 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1470.trans
      change ((114401659 / 70368744177664 : ℚ) : ℝ) ≤ ((457606636 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1470.trans
      change ((1324871520675 / 35184372088832 : ℚ) : ℝ) ≤ ((10598972165400 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1471 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1471.trans
      change ((117363215 / 70368744177664 : ℚ) : ℝ) ≤ ((469452860 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1471.trans
      change ((10440615442581 / 281474976710656 : ℚ) : ℝ) ≤ ((10440615442581 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1472 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1472.trans
      change ((481602023 / 281474976710656 : ℚ) : ℝ) ≤ ((481602023 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1472.trans
      change ((5141095465035 / 140737488355328 : ℚ) : ℝ) ≤ ((10282190930070 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1473 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1473.trans
      change ((123515443 / 70368744177664 : ℚ) : ℝ) ≤ ((494061772 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1473.trans
      change ((10123698584327 / 281474976710656 : ℚ) : ℝ) ≤ ((10123698584327 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1474 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1474.trans
      change ((506839945 / 281474976710656 : ℚ) : ℝ) ≤ ((506839945 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1474.trans
      change ((9965138361777 / 281474976710656 : ℚ) : ℝ) ≤ ((9965138361777 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1475 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1475.trans
      change ((259972287 / 140737488355328 : ℚ) : ℝ) ≤ ((519944574 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1475.trans
      change ((9806510218805 / 281474976710656 : ℚ) : ℝ) ≤ ((9806510218805 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1476 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1476.trans
      change ((133345973 / 70368744177664 : ℚ) : ℝ) ≤ ((533383892 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1476.trans
      change ((4823907055881 / 140737488355328 : ℚ) : ℝ) ≤ ((9647814111762 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1477 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1477.trans
      change ((273583167 / 140737488355328 : ℚ) : ℝ) ≤ ((547166334 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1477.trans
      change ((296532812405 / 8796093022208 : ℚ) : ℝ) ≤ ((9489049996960 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1478 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1478.trans
      change ((561300547 / 281474976710656 : ℚ) : ℝ) ≤ ((561300547 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1478.trans
      change ((583138614417 / 17592186044416 : ℚ) : ℝ) ≤ ((9330217830672 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1479 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1479.trans
      change ((287897697 / 140737488355328 : ℚ) : ℝ) ≤ ((575795394 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1479.trans
      change ((9171317569137 / 281474976710656 : ℚ) : ℝ) ≤ ((9171317569137 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1480 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1480.trans
      change ((590659955 / 281474976710656 : ℚ) : ℝ) ≤ ((590659955 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1480.trans
      change ((1126543646069 / 35184372088832 : ℚ) : ℝ) ≤ ((9012349168552 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1481 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1481.trans
      change ((302951769 / 140737488355328 : ℚ) : ℝ) ≤ ((605903538 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1481.trans
      change ((8853312585081 / 281474976710656 : ℚ) : ℝ) ≤ ((8853312585081 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1482 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1482.trans
      change ((621535681 / 281474976710656 : ℚ) : ℝ) ≤ ((621535681 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1482.trans
      change ((8694207774847 / 281474976710656 : ℚ) : ℝ) ≤ ((8694207774847 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1483 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1483.trans
      change ((637566159 / 281474976710656 : ℚ) : ℝ) ≤ ((637566159 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1483.trans
      change ((8535034693937 / 281474976710656 : ℚ) : ℝ) ≤ ((8535034693937 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1484 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1484.trans
      change ((654004989 / 281474976710656 : ℚ) : ℝ) ≤ ((654004989 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1484.trans
      change ((8375793298401 / 281474976710656 : ℚ) : ℝ) ≤ ((8375793298401 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1485 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1485.trans
      change ((167715609 / 70368744177664 : ℚ) : ℝ) ≤ ((670862436 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1485.trans
      change ((1027060443031 / 35184372088832 : ℚ) : ℝ) ≤ ((8216483544248 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1486 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1486.trans
      change ((344074511 / 140737488355328 : ℚ) : ℝ) ≤ ((688149022 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1486.trans
      change ((8057105387453 / 281474976710656 : ℚ) : ℝ) ≤ ((8057105387453 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1487 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1487.trans
      change ((352937763 / 140737488355328 : ℚ) : ℝ) ≤ ((705875526 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1487.trans
      change ((7897658783951 / 281474976710656 : ℚ) : ℝ) ≤ ((7897658783951 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1488 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1488.trans
      change ((181013249 / 70368744177664 : ℚ) : ℝ) ≤ ((724052996 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1488.trans
      change ((7738143689641 / 281474976710656 : ℚ) : ℝ) ≤ ((7738143689641 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1489 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1489.trans
      change ((742692755 / 281474976710656 : ℚ) : ℝ) ≤ ((742692755 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1489.trans
      change ((1894640015095 / 70368744177664 : ℚ) : ℝ) ≤ ((7578560060380 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1490 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1490.trans
      change ((761806403 / 281474976710656 : ℚ) : ℝ) ≤ ((761806403 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1490.trans
      change ((7418907851993 / 281474976710656 : ℚ) : ℝ) ≤ ((7418907851993 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1491 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1491.trans
      change ((781405829 / 281474976710656 : ℚ) : ℝ) ≤ ((781405829 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1491.trans
      change ((3629593510131 / 140737488355328 : ℚ) : ℝ) ≤ ((7259187020262 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1492 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1492.trans
      change ((801503217 / 281474976710656 : ℚ) : ℝ) ≤ ((801503217 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1492.trans
      change ((3549698760467 / 140737488355328 : ℚ) : ℝ) ≤ ((7099397520934 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1493 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1493.trans
      change ((411055525 / 140737488355328 : ℚ) : ℝ) ≤ ((822111050 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1493.trans
      change ((1734884827429 / 70368744177664 : ℚ) : ℝ) ≤ ((6939539309716 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1494 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1494.trans
      change ((105405265 / 35184372088832 : ℚ) : ℝ) ≤ ((843242120 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1494.trans
      change ((6779612342279 / 281474976710656 : ℚ) : ℝ) ≤ ((6779612342279 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1495 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1495.trans
      change ((27028423 / 8796093022208 : ℚ) : ℝ) ≤ ((864909536 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1495.trans
      change ((6619616574253 / 281474976710656 : ℚ) : ℝ) ≤ ((6619616574253 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1496 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1496.trans
      change ((443563365 / 140737488355328 : ℚ) : ℝ) ≤ ((887126730 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1496.trans
      change ((403721997577 / 17592186044416 : ℚ) : ℝ) ≤ ((6459551961232 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1497 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1497.trans
      change ((909907467 / 281474976710656 : ℚ) : ℝ) ≤ ((909907467 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1497.trans
      change ((6299418458771 / 281474976710656 : ℚ) : ℝ) ≤ ((6299418458771 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1498 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1498.trans
      change ((466632925 / 140737488355328 : ℚ) : ℝ) ≤ ((933265850 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1498.trans
      change ((1534804005597 / 70368744177664 : ℚ) : ℝ) ≤ ((6139216022388 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1499 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1499.trans
      change ((957216329 / 281474976710656 : ℚ) : ℝ) ≤ ((957216329 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1499.trans
      change ((5978944607561 / 281474976710656 : ℚ) : ℝ) ≤ ((5978944607561 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1500 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1500.trans
      change ((981773715 / 281474976710656 : ℚ) : ℝ) ≤ ((981773715 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1500.trans
      change ((2909302084865 / 140737488355328 : ℚ) : ℝ) ≤ ((5818604169730 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1501 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1501.trans
      change ((503476589 / 140737488355328 : ℚ) : ℝ) ≤ ((1006953178 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1501.trans
      change ((5658194664297 / 281474976710656 : ℚ) : ℝ) ≤ ((5658194664297 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1502 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1502.trans
      change ((1032770267 / 281474976710656 : ℚ) : ℝ) ≤ ((1032770267 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1502.trans
      change ((5497716046625 / 281474976710656 : ℚ) : ℝ) ≤ ((5497716046625 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1503 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1503.trans
      change ((1059240911 / 281474976710656 : ℚ) : ℝ) ≤ ((1059240911 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1503.trans
      change ((5337168272041 / 281474976710656 : ℚ) : ℝ) ≤ ((5337168272041 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1504 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1504.trans
      change ((1086381431 / 281474976710656 : ℚ) : ℝ) ≤ ((1086381431 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1504.trans
      change ((5176551295829 / 281474976710656 : ℚ) : ℝ) ≤ ((5176551295829 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1505 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1505.trans
      change ((1114208553 / 281474976710656 : ℚ) : ℝ) ≤ ((1114208553 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1505.trans
      change ((2507932536619 / 140737488355328 : ℚ) : ℝ) ≤ ((5015865073238 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1506 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1506.trans
      change ((1142739411 / 281474976710656 : ℚ) : ℝ) ≤ ((1142739411 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1506.trans
      change ((4855109559477 / 281474976710656 : ℚ) : ℝ) ≤ ((4855109559477 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1507 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1507.trans
      change ((1171991563 / 281474976710656 : ℚ) : ℝ) ≤ ((1171991563 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1507.trans
      change ((4694284709717 / 281474976710656 : ℚ) : ℝ) ≤ ((4694284709717 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1508 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1508.trans
      change ((300495749 / 70368744177664 : ℚ) : ℝ) ≤ ((1201982996 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1508.trans
      change ((4533390479091 / 281474976710656 : ℚ) : ℝ) ≤ ((4533390479091 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1509 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1509.trans
      change ((616366071 / 140737488355328 : ℚ) : ℝ) ≤ ((1232732142 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1509.trans
      change ((2186213411345 / 140737488355328 : ℚ) : ℝ) ≤ ((4372426822690 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1510 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1510.trans
      change ((1264257885 / 281474976710656 : ℚ) : ℝ) ≤ ((1264257885 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1510.trans
      change ((4211393695571 / 281474976710656 : ℚ) : ℝ) ≤ ((4211393695571 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1511 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1511.trans
      change ((648289785 / 140737488355328 : ℚ) : ℝ) ≤ ((1296579570 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1511.trans
      change ((1012572763187 / 70368744177664 : ℚ) : ℝ) ≤ ((4050291052748 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1512 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1512.trans
      change ((664858511 / 140737488355328 : ℚ) : ℝ) ≤ ((1329717022 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1512.trans
      change ((1944559424599 / 140737488355328 : ℚ) : ℝ) ≤ ((3889118849198 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1513 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1513.trans
      change ((340922637 / 70368744177664 : ℚ) : ℝ) ≤ ((1363690548 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1513.trans
      change ((3727877039859 / 281474976710656 : ℚ) : ℝ) ≤ ((3727877039859 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1514 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1514.trans
      change ((1398520957 / 281474976710656 : ℚ) : ℝ) ≤ ((1398520957 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1514.trans
      change ((222910348727 / 17592186044416 : ℚ) : ℝ) ≤ ((3566565579632 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1515 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1515.trans
      change ((358557391 / 70368744177664 : ℚ) : ℝ) ≤ ((1434229564 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1515.trans
      change ((1702592211687 / 140737488355328 : ℚ) : ℝ) ≤ ((3405184423374 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1516 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1516.trans
      change ((1470838211 / 281474976710656 : ℚ) : ℝ) ≤ ((1470838211 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1516.trans
      change ((810933381477 / 70368744177664 : ℚ) : ℝ) ≤ ((3243733525908 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1517 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1517.trans
      change ((188546159 / 35184372088832 : ℚ) : ℝ) ≤ ((1508369272 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1517.trans
      change ((96319151313 / 8796093022208 : ℚ) : ℝ) ≤ ((3082212842016 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1518 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1518.trans
      change ((1546845671 / 281474976710656 : ℚ) : ℝ) ≤ ((1546845671 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1518.trans
      change ((2920622326441 / 281474976710656 : ℚ) : ℝ) ≤ ((2920622326441 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1519 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1519.trans
      change ((396572723 / 70368744177664 : ℚ) : ℝ) ≤ ((1586290892 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1519.trans
      change ((2758961933885 / 281474976710656 : ℚ) : ℝ) ≤ ((2758961933885 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1520 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1520.trans
      change ((813364497 / 140737488355328 : ℚ) : ℝ) ≤ ((1626728994 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1520.trans
      change ((2597231619015 / 281474976710656 : ℚ) : ℝ) ≤ ((2597231619015 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1521 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1521.trans
      change ((1668184627 / 281474976710656 : ℚ) : ℝ) ≤ ((1668184627 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1521.trans
      change ((1217715668227 / 140737488355328 : ℚ) : ℝ) ≤ ((2435431336454 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1522 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1522.trans
      change ((53458845 / 8796093022208 : ℚ) : ℝ) ≤ ((1710683040 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1522.trans
      change ((1136780520395 / 140737488355328 : ℚ) : ℝ) ≤ ((2273561040790 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1523 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1523.trans
      change ((1754250103 / 281474976710656 : ℚ) : ℝ) ≤ ((1754250103 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1523.trans
      change ((1055810343285 / 140737488355328 : ℚ) : ℝ) ≤ ((2111620686570 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1524 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1524.trans
      change ((449728079 / 70368744177664 : ℚ) : ℝ) ≤ ((1798912316 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1524.trans
      change ((1949610228299 / 281474976710656 : ℚ) : ℝ) ≤ ((1949610228299 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1525 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1525.trans
      change ((461174207 / 70368744177664 : ℚ) : ℝ) ≤ ((1844696828 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1525.trans
      change ((55860300639 / 8796093022208 : ℚ) : ℝ) ≤ ((1787529620448 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1526 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1526.trans
      change ((1891631449 / 281474976710656 : ℚ) : ℝ) ≤ ((1891631449 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1526.trans
      change ((1625378817443 / 281474976710656 : ℚ) : ℝ) ≤ ((1625378817443 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1527 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1527.trans
      change ((1939744669 / 281474976710656 : ℚ) : ℝ) ≤ ((1939744669 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1527.trans
      change ((1463157773675 / 281474976710656 : ℚ) : ℝ) ≤ ((1463157773675 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1528 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1528.trans
      change ((1989065675 / 281474976710656 : ℚ) : ℝ) ≤ ((1989065675 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1528.trans
      change ((1300866443493 / 281474976710656 : ℚ) : ℝ) ≤ ((1300866443493 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1529 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1529.trans
      change ((2039624363 / 281474976710656 : ℚ) : ℝ) ≤ ((2039624363 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1529.trans
      change ((569252390603 / 140737488355328 : ℚ) : ℝ) ≤ ((1138504781206 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1530 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1530.trans
      change ((2091451361 / 281474976710656 : ℚ) : ℝ) ≤ ((2091451361 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1530.trans
      change ((488036370543 / 140737488355328 : ℚ) : ℝ) ≤ ((976072741086 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1531 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1531.trans
      change ((268072255 / 35184372088832 : ℚ) : ℝ) ≤ ((2144578040 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1531.trans
      change ((813570277363 / 281474976710656 : ℚ) : ℝ) ≤ ((813570277363 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1532 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1532.trans
      change ((2199036539 / 281474976710656 : ℚ) : ℝ) ≤ ((2199036539 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1532.trans
      change ((650997344229 / 281474976710656 : ℚ) : ℝ) ≤ ((650997344229 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1533 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1533.trans
      change ((1127429889 / 140737488355328 : ℚ) : ℝ) ≤ ((2254859778 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1533.trans
      change ((488353895833 / 281474976710656 : ℚ) : ℝ) ≤ ((488353895833 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1534 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1534.trans
      change ((2312081479 / 281474976710656 : ℚ) : ℝ) ≤ ((2312081479 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1534.trans
      change ((325639886289 / 281474976710656 : ℚ) : ℝ) ≤ ((325639886289 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1535 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma011.sigma_factor_upper_1535.trans
      change ((296342023 / 35184372088832 : ℚ) : ℝ) ≤ ((2370736184 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma011.sigma_power_upper_1535.trans
      change ((162855269667 / 281474976710656 : ℚ) : ℝ) ≤ ((162855269667 : ℕ) : ℝ) / 2^48
      norm_num
end LegendreK6.M2Pilot.FactorBounds.Sigma011
