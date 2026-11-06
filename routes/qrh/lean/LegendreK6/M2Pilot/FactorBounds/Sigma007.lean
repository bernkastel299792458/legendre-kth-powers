import LegendreK6.M2Pilot.Enclosures.Sigma007
import LegendreK6.M2PilotIntegerData

/-! Join checked analytic enclosures to the exact dyadic witness table. -/
namespace LegendreK6.M2Pilot.FactorBounds.Sigma007
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem bounds (i : Fin 1536) (hlo : 896 ≤ i.val) (hhi : i.val < 1024) :
    sigmaFactor i ≤ sigmaDyadicFactor i ∧ sigmaPower i ≤ sigmaDyadicPower i := by
  interval_cases hi : i.val
  · have heq : i = (896 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_896.trans
      change ((5 / 35184372088832 : ℚ) : ℝ) ≤ ((40 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_896.trans
      change ((22884144448021 / 70368744177664 : ℚ) : ℝ) ≤ ((91536577792084 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (897 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_897.trans
      change ((41 / 281474976710656 : ℚ) : ℝ) ≤ ((41 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_897.trans
      change ((91410970138167 / 281474976710656 : ℚ) : ℝ) ≤ ((91410970138167 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (898 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_898.trans
      change ((21 / 140737488355328 : ℚ) : ℝ) ≤ ((42 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_898.trans
      change ((91285314597229 / 281474976710656 : ℚ) : ℝ) ≤ ((91285314597229 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (899 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_899.trans
      change ((43 / 281474976710656 : ℚ) : ℝ) ≤ ((43 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_899.trans
      change ((45579805570941 / 140737488355328 : ℚ) : ℝ) ≤ ((91159611141882 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (900 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_900.trans
      change ((45 / 281474976710656 : ℚ) : ℝ) ≤ ((45 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_900.trans
      change ((91033859744713 / 281474976710656 : ℚ) : ℝ) ≤ ((91033859744713 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (901 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_901.trans
      change ((23 / 140737488355328 : ℚ) : ℝ) ≤ ((46 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_901.trans
      change ((90908060378291 / 281474976710656 : ℚ) : ℝ) ≤ ((90908060378291 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (902 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_902.trans
      change ((47 / 281474976710656 : ℚ) : ℝ) ≤ ((47 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_902.trans
      change ((90782213015163 / 281474976710656 : ℚ) : ℝ) ≤ ((90782213015163 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (903 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_903.trans
      change ((49 / 281474976710656 : ℚ) : ℝ) ≤ ((49 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_903.trans
      change ((90656317627855 / 281474976710656 : ℚ) : ℝ) ≤ ((90656317627855 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (904 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_904.trans
      change ((25 / 140737488355328 : ℚ) : ℝ) ≤ ((50 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_904.trans
      change ((90530374188873 / 281474976710656 : ℚ) : ℝ) ≤ ((90530374188873 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (905 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_905.trans
      change ((51 / 281474976710656 : ℚ) : ℝ) ≤ ((51 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_905.trans
      change ((22601095667675 / 70368744177664 : ℚ) : ℝ) ≤ ((90404382670700 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (906 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_906.trans
      change ((53 / 281474976710656 : ℚ) : ℝ) ≤ ((53 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_906.trans
      change ((90278343045801 / 281474976710656 : ℚ) : ℝ) ≤ ((90278343045801 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (907 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_907.trans
      change ((55 / 281474976710656 : ℚ) : ℝ) ≤ ((55 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_907.trans
      change ((11269031910827 / 35184372088832 : ℚ) : ℝ) ≤ ((90152255286616 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (908 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_908.trans
      change ((7 / 35184372088832 : ℚ) : ℝ) ≤ ((56 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_908.trans
      change ((1406658115087 / 4398046511104 : ℚ) : ℝ) ≤ ((90026119365568 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (909 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_909.trans
      change ((29 / 140737488355328 : ℚ) : ℝ) ≤ ((58 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_909.trans
      change ((5618745953441 / 17592186044416 : ℚ) : ℝ) ≤ ((89899935255056 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (910 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_910.trans
      change ((15 / 70368744177664 : ℚ) : ℝ) ≤ ((60 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_910.trans
      change ((22443425731865 / 70368744177664 : ℚ) : ℝ) ≤ ((89773702927460 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (911 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_911.trans
      change ((61 / 281474976710656 : ℚ) : ℝ) ≤ ((61 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_911.trans
      change ((1400740974299 / 4398046511104 : ℚ) : ℝ) ≤ ((89647422355136 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (912 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_912.trans
      change ((63 / 281474976710656 : ℚ) : ℝ) ≤ ((63 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_912.trans
      change ((89521093510423 / 281474976710656 : ℚ) : ℝ) ≤ ((89521093510423 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (913 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_913.trans
      change ((65 / 281474976710656 : ℚ) : ℝ) ≤ ((65 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_913.trans
      change ((89394716365635 / 281474976710656 : ℚ) : ℝ) ≤ ((89394716365635 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (914 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_914.trans
      change ((67 / 281474976710656 : ℚ) : ℝ) ≤ ((67 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_914.trans
      change ((22317072723267 / 70368744177664 : ℚ) : ℝ) ≤ ((89268290893068 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (915 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_915.trans
      change ((69 / 281474976710656 : ℚ) : ℝ) ≤ ((69 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_915.trans
      change ((89141817064993 / 281474976710656 : ℚ) : ℝ) ≤ ((89141817064993 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (916 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_916.trans
      change ((71 / 281474976710656 : ℚ) : ℝ) ≤ ((71 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_916.trans
      change ((2781727964177 / 8796093022208 : ℚ) : ℝ) ≤ ((89015294853664 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (917 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_917.trans
      change ((73 / 281474976710656 : ℚ) : ℝ) ≤ ((73 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_917.trans
      change ((44444362115655 / 140737488355328 : ℚ) : ℝ) ≤ ((88888724231310 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (918 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_918.trans
      change ((75 / 281474976710656 : ℚ) : ℝ) ≤ ((75 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_918.trans
      change ((44381052585071 / 140737488355328 : ℚ) : ℝ) ≤ ((88762105170142 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (919 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_919.trans
      change ((77 / 281474976710656 : ℚ) : ℝ) ≤ ((77 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_919.trans
      change ((22158859410587 / 70368744177664 : ℚ) : ℝ) ≤ ((88635437642348 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (920 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_920.trans
      change ((5 / 17592186044416 : ℚ) : ℝ) ≤ ((80 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_920.trans
      change ((44254360810047 / 140737488355328 : ℚ) : ℝ) ≤ ((88508721620094 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (921 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_921.trans
      change ((41 / 140737488355328 : ℚ) : ℝ) ≤ ((82 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_921.trans
      change ((88381957075527 / 281474976710656 : ℚ) : ℝ) ≤ ((88381957075527 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (922 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_922.trans
      change ((21 / 70368744177664 : ℚ) : ℝ) ≤ ((84 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_922.trans
      change ((44127571990385 / 140737488355328 : ℚ) : ℝ) ≤ ((88255143980770 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (923 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_923.trans
      change ((87 / 281474976710656 : ℚ) : ℝ) ≤ ((87 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_923.trans
      change ((88128282307927 / 281474976710656 : ℚ) : ℝ) ≤ ((88128282307927 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (924 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_924.trans
      change ((89 / 281474976710656 : ℚ) : ℝ) ≤ ((89 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_924.trans
      change ((88001372029079 / 281474976710656 : ℚ) : ℝ) ≤ ((88001372029079 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (925 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_925.trans
      change ((23 / 70368744177664 : ℚ) : ℝ) ≤ ((92 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_925.trans
      change ((43937206558143 / 140737488355328 : ℚ) : ℝ) ≤ ((87874413116286 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (926 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_926.trans
      change ((95 / 281474976710656 : ℚ) : ℝ) ≤ ((95 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_926.trans
      change ((87747405541587 / 281474976710656 : ℚ) : ℝ) ≤ ((87747405541587 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (927 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_927.trans
      change ((97 / 281474976710656 : ℚ) : ℝ) ≤ ((97 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_927.trans
      change ((10952543659625 / 35184372088832 : ℚ) : ℝ) ≤ ((87620349277000 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (928 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_928.trans
      change ((25 / 70368744177664 : ℚ) : ℝ) ≤ ((100 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_928.trans
      change ((87493244294519 / 281474976710656 : ℚ) : ℝ) ≤ ((87493244294519 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (929 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_929.trans
      change ((103 / 281474976710656 : ℚ) : ℝ) ≤ ((103 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_929.trans
      change ((10920761320765 / 35184372088832 : ℚ) : ℝ) ≤ ((87366090566120 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (930 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_930.trans
      change ((53 / 140737488355328 : ℚ) : ℝ) ≤ ((106 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_930.trans
      change ((21809722015939 / 70368744177664 : ℚ) : ℝ) ≤ ((87238888063756 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (931 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_931.trans
      change ((109 / 281474976710656 : ℚ) : ℝ) ≤ ((109 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_931.trans
      change ((87111636759357 / 281474976710656 : ℚ) : ℝ) ≤ ((87111636759357 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (932 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_932.trans
      change ((113 / 281474976710656 : ℚ) : ℝ) ≤ ((113 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_932.trans
      change ((43492168312417 / 140737488355328 : ℚ) : ℝ) ≤ ((86984336624834 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (933 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_933.trans
      change ((29 / 70368744177664 : ℚ) : ℝ) ≤ ((116 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_933.trans
      change ((43428493816037 / 140737488355328 : ℚ) : ℝ) ≤ ((86856987632074 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (934 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_934.trans
      change ((119 / 281474976710656 : ℚ) : ℝ) ≤ ((119 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_934.trans
      change ((86729589752945 / 281474976710656 : ℚ) : ℝ) ≤ ((86729589752945 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (935 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_935.trans
      change ((123 / 281474976710656 : ℚ) : ℝ) ≤ ((123 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_935.trans
      change ((86602142959291 / 281474976710656 : ℚ) : ℝ) ≤ ((86602142959291 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (936 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_936.trans
      change ((63 / 140737488355328 : ℚ) : ℝ) ≤ ((126 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_936.trans
      change ((10809330902867 / 35184372088832 : ℚ) : ℝ) ≤ ((86474647222936 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (937 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_937.trans
      change ((65 / 140737488355328 : ℚ) : ℝ) ≤ ((130 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_937.trans
      change ((43173551257841 / 140737488355328 : ℚ) : ℝ) ≤ ((86347102515682 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (938 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_938.trans
      change ((67 / 140737488355328 : ℚ) : ℝ) ≤ ((134 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_938.trans
      change ((86219508809309 / 281474976710656 : ℚ) : ℝ) ≤ ((86219508809309 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (939 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_939.trans
      change ((69 / 140737488355328 : ℚ) : ℝ) ≤ ((138 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_939.trans
      change ((86091866075575 / 281474976710656 : ℚ) : ℝ) ≤ ((86091866075575 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (940 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_940.trans
      change ((71 / 140737488355328 : ℚ) : ℝ) ≤ ((142 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_940.trans
      change ((85964174286217 / 281474976710656 : ℚ) : ℝ) ≤ ((85964174286217 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (941 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_941.trans
      change ((73 / 140737488355328 : ℚ) : ℝ) ≤ ((146 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_941.trans
      change ((42918216706475 / 140737488355328 : ℚ) : ℝ) ≤ ((85836433412950 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (942 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_942.trans
      change ((75 / 140737488355328 : ℚ) : ℝ) ≤ ((150 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_942.trans
      change ((85708643427467 / 281474976710656 : ℚ) : ℝ) ≤ ((85708643427467 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (943 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_943.trans
      change ((155 / 281474976710656 : ℚ) : ℝ) ≤ ((155 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_943.trans
      change ((85580804301439 / 281474976710656 : ℚ) : ℝ) ≤ ((85580804301439 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (944 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_944.trans
      change ((159 / 281474976710656 : ℚ) : ℝ) ≤ ((159 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_944.trans
      change ((42726458003259 / 140737488355328 : ℚ) : ℝ) ≤ ((85452916006518 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (945 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_945.trans
      change ((41 / 70368744177664 : ℚ) : ℝ) ≤ ((164 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_945.trans
      change ((85324978514329 / 281474976710656 : ℚ) : ℝ) ≤ ((85324978514329 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (946 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_946.trans
      change ((169 / 281474976710656 : ℚ) : ℝ) ≤ ((169 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_946.trans
      change ((332800749205 / 1099511627776 : ℚ) : ℝ) ≤ ((85196991796480 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (947 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_947.trans
      change ((87 / 140737488355328 : ℚ) : ℝ) ≤ ((174 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_947.trans
      change ((42534477912277 / 140737488355328 : ℚ) : ℝ) ≤ ((85068955824554 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (948 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_948.trans
      change ((179 / 281474976710656 : ℚ) : ℝ) ≤ ((179 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_948.trans
      change ((42470435285057 / 140737488355328 : ℚ) : ℝ) ≤ ((84940870570114 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (949 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_949.trans
      change ((23 / 35184372088832 : ℚ) : ℝ) ≤ ((184 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_949.trans
      change ((21203184001175 / 70368744177664 : ℚ) : ℝ) ≤ ((84812736004700 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (950 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_950.trans
      change ((95 / 140737488355328 : ℚ) : ℝ) ≤ ((190 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_950.trans
      change ((84684552099831 / 281474976710656 : ℚ) : ℝ) ≤ ((84684552099831 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (951 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_951.trans
      change ((195 / 281474976710656 : ℚ) : ℝ) ≤ ((195 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_951.trans
      change ((84556318827003 / 281474976710656 : ℚ) : ℝ) ≤ ((84556318827003 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (952 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_952.trans
      change ((201 / 281474976710656 : ℚ) : ℝ) ≤ ((201 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_952.trans
      change ((84428036157691 / 281474976710656 : ℚ) : ℝ) ≤ ((84428036157691 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (953 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_953.trans
      change ((207 / 281474976710656 : ℚ) : ℝ) ≤ ((207 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_953.trans
      change ((84299704063347 / 281474976710656 : ℚ) : ℝ) ≤ ((84299704063347 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (954 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_954.trans
      change ((213 / 281474976710656 : ℚ) : ℝ) ≤ ((213 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_954.trans
      change ((84171322515403 / 281474976710656 : ℚ) : ℝ) ≤ ((84171322515403 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (955 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_955.trans
      change ((219 / 281474976710656 : ℚ) : ℝ) ≤ ((219 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_955.trans
      change ((42021445742633 / 140737488355328 : ℚ) : ℝ) ≤ ((84042891485266 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (956 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_956.trans
      change ((225 / 281474976710656 : ℚ) : ℝ) ≤ ((225 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_956.trans
      change ((20978602736081 / 70368744177664 : ℚ) : ℝ) ≤ ((83914410944324 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (957 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_957.trans
      change ((29 / 35184372088832 : ℚ) : ℝ) ≤ ((232 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_957.trans
      change ((20946470215985 / 70368744177664 : ℚ) : ℝ) ≤ ((83785880863940 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (958 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_958.trans
      change ((239 / 281474976710656 : ℚ) : ℝ) ≤ ((239 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_958.trans
      change ((83657301215457 / 281474976710656 : ℚ) : ℝ) ≤ ((83657301215457 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (959 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_959.trans
      change ((123 / 140737488355328 : ℚ) : ℝ) ≤ ((246 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_959.trans
      change ((20882167992549 / 70368744177664 : ℚ) : ℝ) ≤ ((83528671970196 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (960 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_960.trans
      change ((253 / 281474976710656 : ℚ) : ℝ) ≤ ((253 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_960.trans
      change ((41699996549727 / 140737488355328 : ℚ) : ℝ) ≤ ((83399993099454 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (961 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_961.trans
      change ((261 / 281474976710656 : ℚ) : ℝ) ≤ ((261 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_961.trans
      change ((20817816143627 / 70368744177664 : ℚ) : ℝ) ≤ ((83271264574508 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (962 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_962.trans
      change ((67 / 70368744177664 : ℚ) : ℝ) ≤ ((268 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_962.trans
      change ((83142486366611 / 281474976710656 : ℚ) : ℝ) ≤ ((83142486366611 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (963 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_963.trans
      change ((69 / 70368744177664 : ℚ) : ℝ) ≤ ((276 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_963.trans
      change ((20753414611749 / 70368744177664 : ℚ) : ℝ) ≤ ((83013658446996 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (964 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_964.trans
      change ((71 / 70368744177664 : ℚ) : ℝ) ≤ ((284 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_964.trans
      change ((82884780786871 / 281474976710656 : ℚ) : ℝ) ≤ ((82884780786871 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (965 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_965.trans
      change ((73 / 70368744177664 : ℚ) : ℝ) ≤ ((292 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_965.trans
      change ((82755853357423 / 281474976710656 : ℚ) : ℝ) ≤ ((82755853357423 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (966 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_966.trans
      change ((301 / 281474976710656 : ℚ) : ℝ) ≤ ((301 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_966.trans
      change ((41313438064909 / 140737488355328 : ℚ) : ℝ) ≤ ((82626876129818 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (967 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_967.trans
      change ((155 / 140737488355328 : ℚ) : ℝ) ≤ ((310 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_967.trans
      change ((82497849075199 / 281474976710656 : ℚ) : ℝ) ≤ ((82497849075199 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (968 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_968.trans
      change ((319 / 281474976710656 : ℚ) : ℝ) ≤ ((319 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_968.trans
      change ((82368772164685 / 281474976710656 : ℚ) : ℝ) ≤ ((82368772164685 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (969 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_969.trans
      change ((41 / 35184372088832 : ℚ) : ℝ) ≤ ((328 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_969.trans
      change ((82239645369375 / 281474976710656 : ℚ) : ℝ) ≤ ((82239645369375 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (970 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_970.trans
      change ((169 / 140737488355328 : ℚ) : ℝ) ≤ ((338 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_970.trans
      change ((10263808582543 / 35184372088832 : ℚ) : ℝ) ≤ ((82110468660344 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (971 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_971.trans
      change ((87 / 70368744177664 : ℚ) : ℝ) ≤ ((348 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_971.trans
      change ((40990621004323 / 140737488355328 : ℚ) : ℝ) ≤ ((81981242008646 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (972 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_972.trans
      change ((179 / 140737488355328 : ℚ) : ℝ) ≤ ((358 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_972.trans
      change ((81851965385311 / 281474976710656 : ℚ) : ℝ) ≤ ((81851965385311 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (973 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_973.trans
      change ((23 / 17592186044416 : ℚ) : ℝ) ≤ ((368 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_973.trans
      change ((81722638761349 / 281474976710656 : ℚ) : ℝ) ≤ ((81722638761349 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (974 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_974.trans
      change ((379 / 281474976710656 : ℚ) : ℝ) ≤ ((379 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_974.trans
      change ((2549789440867 / 8796093022208 : ℚ) : ℝ) ≤ ((81593262107744 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (975 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_975.trans
      change ((195 / 140737488355328 : ℚ) : ℝ) ≤ ((390 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_975.trans
      change ((40731917697731 / 140737488355328 : ℚ) : ℝ) ≤ ((81463835395462 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (976 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_976.trans
      change ((201 / 140737488355328 : ℚ) : ℝ) ≤ ((402 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_976.trans
      change ((81334358595443 / 281474976710656 : ℚ) : ℝ) ≤ ((81334358595443 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (977 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_977.trans
      change ((413 / 281474976710656 : ℚ) : ℝ) ≤ ((413 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_977.trans
      change ((81204831678605 / 281474976710656 : ℚ) : ℝ) ≤ ((81204831678605 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (978 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_978.trans
      change ((425 / 281474976710656 : ℚ) : ℝ) ≤ ((425 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_978.trans
      change ((40537627307923 / 140737488355328 : ℚ) : ℝ) ≤ ((81075254615846 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (979 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_979.trans
      change ((219 / 140737488355328 : ℚ) : ℝ) ≤ ((438 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_979.trans
      change ((80945627378037 / 281474976710656 : ℚ) : ℝ) ≤ ((80945627378037 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (980 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_980.trans
      change ((451 / 281474976710656 : ℚ) : ℝ) ≤ ((451 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_980.trans
      change ((2525498435501 / 8796093022208 : ℚ) : ℝ) ≤ ((80815949936032 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (981 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_981.trans
      change ((29 / 17592186044416 : ℚ) : ℝ) ≤ ((464 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_981.trans
      change ((80686222260657 / 281474976710656 : ℚ) : ℝ) ≤ ((80686222260657 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (982 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_982.trans
      change ((477 / 281474976710656 : ℚ) : ℝ) ≤ ((477 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_982.trans
      change ((2517388885085 / 8796093022208 : ℚ) : ℝ) ≤ ((80556444322720 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (983 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_983.trans
      change ((491 / 281474976710656 : ℚ) : ℝ) ≤ ((491 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_983.trans
      change ((40213308046501 / 140737488355328 : ℚ) : ℝ) ≤ ((80426616093002 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (984 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_984.trans
      change ((253 / 140737488355328 : ℚ) : ℝ) ≤ ((506 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_984.trans
      change ((80296737542265 / 281474976710656 : ℚ) : ℝ) ≤ ((80296737542265 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (985 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_985.trans
      change ((65 / 35184372088832 : ℚ) : ℝ) ≤ ((520 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_985.trans
      change ((80166808641247 / 281474976710656 : ℚ) : ℝ) ≤ ((80166808641247 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (986 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_986.trans
      change ((67 / 35184372088832 : ℚ) : ℝ) ≤ ((536 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_986.trans
      change ((80036829360663 / 281474976710656 : ℚ) : ℝ) ≤ ((80036829360663 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (987 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_987.trans
      change ((551 / 281474976710656 : ℚ) : ℝ) ≤ ((551 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_987.trans
      change ((79906799671205 / 281474976710656 : ℚ) : ℝ) ≤ ((79906799671205 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (988 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_988.trans
      change ((567 / 281474976710656 : ℚ) : ℝ) ≤ ((567 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_988.trans
      change ((79776719543543 / 281474976710656 : ℚ) : ℝ) ≤ ((79776719543543 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (989 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_989.trans
      change ((73 / 35184372088832 : ℚ) : ℝ) ≤ ((584 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_989.trans
      change ((19911647237081 / 70368744177664 : ℚ) : ℝ) ≤ ((79646588948324 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (990 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_990.trans
      change ((601 / 281474976710656 : ℚ) : ℝ) ≤ ((601 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_990.trans
      change ((79516407856173 / 281474976710656 : ℚ) : ℝ) ≤ ((79516407856173 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (991 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_991.trans
      change ((309 / 140737488355328 : ℚ) : ℝ) ≤ ((618 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_991.trans
      change ((79386176237691 / 281474976710656 : ℚ) : ℝ) ≤ ((79386176237691 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (992 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_992.trans
      change ((159 / 70368744177664 : ℚ) : ℝ) ≤ ((636 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_992.trans
      change ((2476746689483 / 8796093022208 : ℚ) : ℝ) ≤ ((79255894063456 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (993 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_993.trans
      change ((655 / 281474976710656 : ℚ) : ℝ) ≤ ((655 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_993.trans
      change ((79125561304025 / 281474976710656 : ℚ) : ℝ) ≤ ((79125561304025 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (994 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_994.trans
      change ((337 / 140737488355328 : ℚ) : ℝ) ≤ ((674 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_994.trans
      change ((39497588964965 / 140737488355328 : ℚ) : ℝ) ≤ ((78995177929930 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (995 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_995.trans
      change ((347 / 140737488355328 : ℚ) : ℝ) ≤ ((694 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_995.trans
      change ((308065405905 / 1099511627776 : ℚ) : ℝ) ≤ ((78864743911680 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (996 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_996.trans
      change ((357 / 140737488355328 : ℚ) : ℝ) ≤ ((714 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_996.trans
      change ((19683564804941 / 70368744177664 : ℚ) : ℝ) ≤ ((78734259219764 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (997 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_997.trans
      change ((735 / 281474976710656 : ℚ) : ℝ) ≤ ((735 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_997.trans
      change ((39301861912323 / 140737488355328 : ℚ) : ℝ) ≤ ((78603723824646 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (998 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_998.trans
      change ((189 / 70368744177664 : ℚ) : ℝ) ≤ ((756 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_998.trans
      change ((39236568848383 / 140737488355328 : ℚ) : ℝ) ≤ ((78473137696766 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (999 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_999.trans
      change ((389 / 140737488355328 : ℚ) : ℝ) ≤ ((778 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_999.trans
      change ((78342500806543 / 281474976710656 : ℚ) : ℝ) ≤ ((78342500806543 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1000 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_1000.trans
      change ((801 / 281474976710656 : ℚ) : ℝ) ≤ ((801 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_1000.trans
      change ((78211813124371 / 281474976710656 : ℚ) : ℝ) ≤ ((78211813124371 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1001 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_1001.trans
      change ((103 / 35184372088832 : ℚ) : ℝ) ≤ ((824 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_1001.trans
      change ((4880067163789 / 17592186044416 : ℚ) : ℝ) ≤ ((78081074620624 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1002 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_1002.trans
      change ((53 / 17592186044416 : ℚ) : ℝ) ≤ ((848 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_1002.trans
      change ((77950285265651 / 281474976710656 : ℚ) : ℝ) ≤ ((77950285265651 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1003 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_1003.trans
      change ((873 / 281474976710656 : ℚ) : ℝ) ≤ ((873 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_1003.trans
      change ((77819445029777 / 281474976710656 : ℚ) : ℝ) ≤ ((77819445029777 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1004 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_1004.trans
      change ((449 / 140737488355328 : ℚ) : ℝ) ≤ ((898 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_1004.trans
      change ((77688553883305 / 281474976710656 : ℚ) : ℝ) ≤ ((77688553883305 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1005 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_1005.trans
      change ((231 / 70368744177664 : ℚ) : ℝ) ≤ ((924 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_1005.trans
      change ((77557611796515 / 281474976710656 : ℚ) : ℝ) ≤ ((77557611796515 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1006 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_1006.trans
      change ((951 / 281474976710656 : ℚ) : ℝ) ≤ ((951 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_1006.trans
      change ((77426618739665 / 281474976710656 : ℚ) : ℝ) ≤ ((77426618739665 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1007 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_1007.trans
      change ((979 / 281474976710656 : ℚ) : ℝ) ≤ ((979 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_1007.trans
      change ((38647787341493 / 140737488355328 : ℚ) : ℝ) ≤ ((77295574682986 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1008 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_1008.trans
      change ((1007 / 281474976710656 : ℚ) : ℝ) ≤ ((1007 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_1008.trans
      change ((77164479596691 / 281474976710656 : ℚ) : ℝ) ≤ ((77164479596691 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1009 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_1009.trans
      change ((1037 / 281474976710656 : ℚ) : ℝ) ≤ ((1037 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_1009.trans
      change ((38516666725483 / 140737488355328 : ℚ) : ℝ) ≤ ((77033333450966 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1010 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_1010.trans
      change ((1067 / 281474976710656 : ℚ) : ℝ) ≤ ((1067 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_1010.trans
      change ((76902136215975 / 281474976710656 : ℚ) : ℝ) ≤ ((76902136215975 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1011 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_1011.trans
      change ((549 / 140737488355328 : ℚ) : ℝ) ≤ ((1098 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_1011.trans
      change ((76770887861859 / 281474976710656 : ℚ) : ℝ) ≤ ((76770887861859 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1012 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_1012.trans
      change ((565 / 140737488355328 : ℚ) : ℝ) ≤ ((1130 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_1012.trans
      change ((76639588358735 / 281474976710656 : ℚ) : ℝ) ≤ ((76639588358735 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1013 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_1013.trans
      change ((581 / 140737488355328 : ℚ) : ℝ) ≤ ((1162 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_1013.trans
      change ((76508237676697 / 281474976710656 : ℚ) : ℝ) ≤ ((76508237676697 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1014 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_1014.trans
      change ((299 / 70368744177664 : ℚ) : ℝ) ≤ ((1196 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_1014.trans
      change ((9547104473227 / 35184372088832 : ℚ) : ℝ) ≤ ((76376835785816 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1015 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_1015.trans
      change ((1231 / 281474976710656 : ℚ) : ℝ) ≤ ((1231 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_1015.trans
      change ((19061345664035 / 70368744177664 : ℚ) : ℝ) ≤ ((76245382656140 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1016 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_1016.trans
      change ((1267 / 281474976710656 : ℚ) : ℝ) ≤ ((1267 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_1016.trans
      change ((19028469564423 / 70368744177664 : ℚ) : ℝ) ≤ ((76113878257692 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1017 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_1017.trans
      change ((1303 / 281474976710656 : ℚ) : ℝ) ≤ ((1303 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_1017.trans
      change ((37991161280237 / 140737488355328 : ℚ) : ℝ) ≤ ((75982322560474 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1018 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_1018.trans
      change ((1341 / 281474976710656 : ℚ) : ℝ) ≤ ((1341 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_1018.trans
      change ((75850715534463 / 281474976710656 : ℚ) : ℝ) ≤ ((75850715534463 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1019 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_1019.trans
      change ((345 / 70368744177664 : ℚ) : ℝ) ≤ ((1380 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_1019.trans
      change ((18929764287403 / 70368744177664 : ℚ) : ℝ) ≤ ((75719057149612 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1020 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_1020.trans
      change ((355 / 70368744177664 : ℚ) : ℝ) ≤ ((1420 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_1020.trans
      change ((18896836843963 / 70368744177664 : ℚ) : ℝ) ≤ ((75587347375852 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1021 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_1021.trans
      change ((1461 / 281474976710656 : ℚ) : ℝ) ≤ ((1461 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_1021.trans
      change ((37727793091545 / 140737488355328 : ℚ) : ℝ) ≤ ((75455586183090 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1022 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_1022.trans
      change ((47 / 8796093022208 : ℚ) : ℝ) ≤ ((1504 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_1022.trans
      change ((75323773541209 / 281474976710656 : ℚ) : ℝ) ≤ ((75323773541209 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (1023 : Fin 1536) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Sigma007.sigma_factor_upper_1023.trans
      change ((1547 / 281474976710656 : ℚ) : ℝ) ≤ ((1547 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Sigma007.sigma_power_upper_1023.trans
      change ((37595954710035 / 140737488355328 : ℚ) : ℝ) ≤ ((75191909420070 : ℕ) : ℝ) / 2^48
      norm_num
end LegendreK6.M2Pilot.FactorBounds.Sigma007
