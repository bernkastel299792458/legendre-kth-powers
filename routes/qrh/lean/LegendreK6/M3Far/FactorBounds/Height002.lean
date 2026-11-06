import LegendreK6.M3Far.Enclosures.Height002
import LegendreK6.M3FarIntegerData

/-! Join checked analytic enclosures to the exact dyadic witness table. -/
namespace LegendreK6.M3Far.FactorBounds.Height002
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem bounds (i : Fin 125) (hlo : 64 ≤ i.val) (hhi : i.val < 96) :
    heightFactor i ≤ heightDyadicFactor i ∧ heightPower i ≤ heightDyadicPower i := by
  interval_cases hi : i.val
  · have heq : i = (64 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height002.height_factor_upper_64.trans
      change ((80761584466507 / 281474976710656 : ℚ) : ℝ) ≤ ((80761584466507 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height002.height_power_upper_64.trans
      change ((2301759045870727 / 281474976710656 : ℚ) : ℝ) ≤ ((2301759045870727 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (65 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height002.height_factor_upper_65.trans
      change ((65751315891499 / 281474976710656 : ℚ) : ℝ) ≤ ((65751315891499 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height002.height_power_upper_65.trans
      change ((2337270524302835 / 281474976710656 : ℚ) : ℝ) ≤ ((2337270524302835 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (66 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height002.height_factor_upper_66.trans
      change ((26765336300837 / 140737488355328 : ℚ) : ℝ) ≤ ((53530672601674 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height002.height_power_upper_66.trans
      change ((2372781623040901 / 281474976710656 : ℚ) : ℝ) ≤ ((2372781623040901 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (67 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height002.height_factor_upper_67.trans
      change ((43581240531479 / 281474976710656 : ℚ) : ℝ) ≤ ((43581240531479 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height002.height_power_upper_67.trans
      change ((18814783929417 / 2199023255552 : ℚ) : ℝ) ≤ ((2408292342965376 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (68 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height002.height_factor_upper_68.trans
      change ((8870234976439 / 70368744177664 : ℚ) : ℝ) ≤ ((35480939905756 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height002.height_power_upper_68.trans
      change ((1221901342476825 / 140737488355328 : ℚ) : ℝ) ≤ ((2443802684953650 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (69 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height002.height_factor_upper_69.trans
      change ((28886125036209 / 281474976710656 : ℚ) : ℝ) ≤ ((28886125036209 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height002.height_power_upper_69.trans
      change ((309914081235009 / 35184372088832 : ℚ) : ℝ) ≤ ((2479312649880072 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (70 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height002.height_factor_upper_70.trans
      change ((5879252501601 / 70368744177664 : ℚ) : ℝ) ≤ ((23517010006404 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height002.height_power_upper_70.trans
      change ((628705559653989 / 70368744177664 : ℚ) : ℝ) ≤ ((2514822238615956 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (71 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height002.height_factor_upper_71.trans
      change ((19145802328831 / 281474976710656 : ℚ) : ℝ) ≤ ((19145802328831 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height002.height_power_upper_71.trans
      change ((1275165726014801 / 140737488355328 : ℚ) : ℝ) ≤ ((2550331452029602 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (72 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height002.height_factor_upper_72.trans
      change ((15587041452805 / 281474976710656 : ℚ) : ℝ) ≤ ((15587041452805 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height002.height_power_upper_72.trans
      change ((2585840290986307 / 281474976710656 : ℚ) : ℝ) ≤ ((2585840290986307 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (73 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height002.height_factor_upper_73.trans
      change ((6344866236093 / 140737488355328 : ℚ) : ℝ) ≤ ((12689732472186 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height002.height_power_upper_73.trans
      change ((2621348756348377 / 281474976710656 : ℚ) : ℝ) ≤ ((2621348756348377 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (74 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height002.height_factor_upper_74.trans
      change ((10330941488299 / 281474976710656 : ℚ) : ℝ) ≤ ((10330941488299 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height002.height_power_upper_74.trans
      change ((1328428424487573 / 140737488355328 : ℚ) : ℝ) ≤ ((2656856848975146 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (75 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height002.height_factor_upper_75.trans
      change ((4205290525701 / 140737488355328 : ℚ) : ℝ) ≤ ((8410581051402 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height002.height_power_upper_75.trans
      change ((2692364569722985 / 281474976710656 : ℚ) : ℝ) ≤ ((2692364569722985 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (76 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height002.height_factor_upper_76.trans
      change ((3423582279995 / 140737488355328 : ℚ) : ℝ) ≤ ((6847164559990 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height002.height_power_upper_76.trans
      change ((2727871919445315 / 281474976710656 : ℚ) : ℝ) ≤ ((2727871919445315 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (77 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height002.height_factor_upper_77.trans
      change ((2787174789801 / 140737488355328 : ℚ) : ℝ) ≤ ((5574349579602 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height002.height_power_upper_77.trans
      change ((1381689449496313 / 140737488355328 : ℚ) : ℝ) ≤ ((2763378898992626 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (78 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height002.height_factor_upper_78.trans
      change ((4538123492923 / 281474976710656 : ℚ) : ℝ) ≤ ((4538123492923 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height002.height_power_upper_78.trans
      change ((1399442754606243 / 140737488355328 : ℚ) : ℝ) ≤ ((2798885509212486 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (79 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height002.height_factor_upper_79.trans
      change ((461814016077 / 35184372088832 : ℚ) : ℝ) ≤ ((3694512128616 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height002.height_power_upper_79.trans
      change ((1417195875474777 / 140737488355328 : ℚ) : ℝ) ≤ ((2834391750949554 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (80 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height002.height_factor_upper_80.trans
      change ((3007714192007 / 281474976710656 : ℚ) : ℝ) ≤ ((3007714192007 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height002.height_power_upper_80.trans
      change ((717474406261399 / 70368744177664 : ℚ) : ℝ) ≤ ((2869897625045596 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (81 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height002.height_factor_upper_81.trans
      change ((2448582376477 / 281474976710656 : ℚ) : ℝ) ≤ ((2448582376477 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height002.height_power_upper_81.trans
      change ((2905403132339497 / 281474976710656 : ℚ) : ℝ) ≤ ((2905403132339497 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (82 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height002.height_factor_upper_82.trans
      change ((1993386735487 / 281474976710656 : ℚ) : ℝ) ≤ ((1993386735487 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height002.height_power_upper_82.trans
      change ((2940908273667273 / 281474976710656 : ℚ) : ℝ) ≤ ((2940908273667273 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (83 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height002.height_factor_upper_83.trans
      change ((1622807864977 / 281474976710656 : ℚ) : ℝ) ≤ ((1622807864977 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height002.height_power_upper_83.trans
      change ((2976413049862085 / 281474976710656 : ℚ) : ℝ) ≤ ((2976413049862085 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (84 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height002.height_factor_upper_84.trans
      change ((660558595821 / 140737488355328 : ℚ) : ℝ) ≤ ((1321117191642 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height002.height_power_upper_84.trans
      change ((1505958730877127 / 140737488355328 : ℚ) : ℝ) ≤ ((3011917461754254 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (85 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height002.height_factor_upper_85.trans
      change ((268877399421 / 70368744177664 : ℚ) : ℝ) ≤ ((1075509597684 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height002.height_power_upper_85.trans
      change ((3047421510171269 / 281474976710656 : ℚ) : ℝ) ≤ ((3047421510171269 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (86 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height002.height_factor_upper_86.trans
      change ((875560073341 / 281474976710656 : ℚ) : ℝ) ≤ ((875560073341 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height002.height_power_upper_86.trans
      change ((3082925195937807 / 281474976710656 : ℚ) : ℝ) ≤ ((3082925195937807 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (87 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height002.height_factor_upper_87.trans
      change ((178195337187 / 70368744177664 : ℚ) : ℝ) ≤ ((712781348748 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height002.height_power_upper_87.trans
      change ((3118428519875737 / 281474976710656 : ℚ) : ℝ) ≤ ((3118428519875737 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (88 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height002.height_factor_upper_88.trans
      change ((290131869813 / 140737488355328 : ℚ) : ℝ) ≤ ((580263739626 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height002.height_power_upper_88.trans
      change ((3153931482804139 / 281474976710656 : ℚ) : ℝ) ≤ ((3153931482804139 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (89 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height002.height_factor_upper_89.trans
      change ((472381928329 / 281474976710656 : ℚ) : ℝ) ≤ ((472381928329 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height002.height_power_upper_89.trans
      change ((3189434085539317 / 281474976710656 : ℚ) : ℝ) ≤ ((3189434085539317 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (90 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height002.height_factor_upper_90.trans
      change ((384556240945 / 281474976710656 : ℚ) : ℝ) ≤ ((384556240945 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height002.height_power_upper_90.trans
      change ((3224936328894807 / 281474976710656 : ℚ) : ℝ) ≤ ((3224936328894807 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (91 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height002.height_factor_upper_91.trans
      change ((313058292737 / 281474976710656 : ℚ) : ℝ) ≤ ((313058292737 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height002.height_power_upper_91.trans
      change ((3260438213681391 / 281474976710656 : ℚ) : ℝ) ≤ ((3260438213681391 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (92 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height002.height_factor_upper_92.trans
      change ((254852756243 / 281474976710656 : ℚ) : ℝ) ≤ ((254852756243 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height002.height_power_upper_92.trans
      change ((1647969870353557 / 140737488355328 : ℚ) : ℝ) ≤ ((3295939740707114 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (93 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height002.height_factor_upper_93.trans
      change ((207468538705 / 281474976710656 : ℚ) : ℝ) ≤ ((207468538705 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height002.height_power_upper_93.trans
      change ((3331440910777289 / 281474976710656 : ℚ) : ℝ) ≤ ((3331440910777289 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (94 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height002.height_factor_upper_94.trans
      change ((168893903075 / 281474976710656 : ℚ) : ℝ) ≤ ((168893903075 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height002.height_power_upper_94.trans
      change ((3366941724694515 / 281474976710656 : ℚ) : ℝ) ≤ ((3366941724694515 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (95 : Fin 125) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height002.height_factor_upper_95.trans
      change ((68745541293 / 140737488355328 : ℚ) : ℝ) ≤ ((137491082586 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height002.height_power_upper_95.trans
      change ((3402442183258687 / 281474976710656 : ℚ) : ℝ) ≤ ((3402442183258687 : ℕ) : ℝ) / 2^48
      norm_num
end LegendreK6.M3Far.FactorBounds.Height002
