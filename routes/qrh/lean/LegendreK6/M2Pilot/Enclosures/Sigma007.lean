import LegendreK6.M2PilotDefinitions
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp

/-! Generated proposals: every bound is checked by Lean, not by trusting Arb. -/
namespace LegendreK6.M2Pilot.Enclosures.Sigma007
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem sigma_factor_upper_896 : sigmaFactor (896 : Fin 1536) ≤ ((5 / 35184372088832 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-19523581 / 671744 : ℚ) : ℝ) - Real.exp ((-152757 / 5248 : ℚ) : ℝ)) ≤ ((5 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_896 : sigmaPower (896 : Fin 1536) ≤ ((22884144448021 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_897 : sigmaFactor (897 : Fin 1536) ≤ ((41 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-37818539 / 1302528 : ℚ) : ℝ) - Real.exp ((-75750763 / 2605056 : ℚ) : ℝ)) ≤ ((41 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_897 : sigmaPower (897 : Fin 1536) ≤ ((91410970138167 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_898 : sigmaFactor (898 : Fin 1536) ≤ ((21 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-1246515105 / 42975232 : ℚ) : ℝ) - Real.exp ((-624195275 / 21487616 : ℚ) : ℝ)) ≤ ((21 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_898 : sigmaPower (898 : Fin 1536) ≤ ((91285314597229 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_899 : sigmaFactor (899 : Fin 1536) ≤ ((43 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-622509569 / 21483520 : ℚ) : ℝ) - Real.exp ((-2493788451 / 85934080 : ℚ) : ℝ)) ≤ ((43 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_899 : sigmaPower (899 : Fin 1536) ≤ ((45579805570941 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_900 : sigmaFactor (900 : Fin 1536) ≤ ((45 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-207253981 / 7159808 : ℚ) : ℝ) - Real.exp ((-51891609 / 1789952 : ℚ) : ℝ)) ≤ ((45 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_900 : sigmaPower (900 : Fin 1536) ≤ ((91033859744713 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_901 : sigmaFactor (901 : Fin 1536) ≤ ((23 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-1242029349 / 42950656 : ℚ) : ℝ) - Real.exp ((-2487807443 / 85901312 : ℚ) : ℝ)) ≤ ((23 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_901 : sigmaPower (901 : Fin 1536) ≤ ((90908060378291 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_902 : sigmaFactor (902 : Fin 1536) ≤ ((47 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-1240535527 / 42942464 : ℚ) : ℝ) - Real.exp ((-621204771 / 21471232 : ℚ) : ℝ)) ≤ ((47 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_902 : sigmaPower (902 : Fin 1536) ≤ ((90782213015163 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_903 : sigmaFactor (903 : Fin 1536) ≤ ((49 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-103253535 / 3577856 : ℚ) : ℝ) - Real.exp ((-827277385 / 28622848 : ℚ) : ℝ)) ≤ ((49 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_903 : sigmaPower (903 : Fin 1536) ≤ ((90656317627855 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_904 : sigmaFactor (904 : Fin 1536) ≤ ((25 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-309387507 / 10731520 : ℚ) : ℝ) - Real.exp ((-38731979 / 1341440 : ℚ) : ℝ)) ≤ ((25 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_904 : sigmaPower (904 : Fin 1536) ≤ ((90530374188873 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_905 : sigmaFactor (905 : Fin 1536) ≤ ((51 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-1236058351 / 42917888 : ℚ) : ℝ) - Real.exp ((-2475862587 / 85835776 : ℚ) : ℝ)) ≤ ((51 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_905 : sigmaPower (905 : Fin 1536) ≤ ((22601095667675 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_906 : sigmaFactor (906 : Fin 1536) ≤ ((53 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-411522463 / 14303232 : ℚ) : ℝ) - Real.exp ((-206073329 / 7151616 : ℚ) : ℝ)) ≤ ((53 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_906 : sigmaPower (906 : Fin 1536) ≤ ((90278343045801 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_907 : sigmaFactor (907 : Fin 1536) ≤ ((55 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-616538571 / 21450752 : ℚ) : ℝ) - Real.exp ((-2469898739 / 85803008 : ℚ) : ℝ)) ≤ ((55 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_907 : sigmaPower (907 : Fin 1536) ≤ ((11269031910827 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_908 : sigmaFactor (908 : Fin 1536) ≤ ((7 / 35184372088832 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-3293015 / 114688 : ℚ) : ℝ) - Real.exp ((-824505 / 28672 : ℚ) : ℝ)) ≤ ((7 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_908 : sigmaPower (908 : Fin 1536) ≤ ((1406658115087 / 4398046511104 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_909 : sigmaFactor (909 : Fin 1536) ≤ ((29 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-410032931 / 14295040 : ℚ) : ℝ) - Real.exp ((-821313537 / 28590080 : ℚ) : ℝ)) ≤ ((29 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_909 : sigmaPower (909 : Fin 1536) ≤ ((5618745953441 / 17592186044416 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_910 : sigmaFactor (910 : Fin 1536) ≤ ((15 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-1228610691 / 42876928 : ℚ) : ℝ) - Real.exp ((-615240923 / 21438464 : ℚ) : ℝ)) ≤ ((15 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_910 : sigmaPower (910 : Fin 1536) ≤ ((22443425731865 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_911 : sigmaFactor (911 : Fin 1536) ≤ ((61 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-153390413 / 5358592 : ℚ) : ℝ) - Real.exp ((-2457988203 / 85737472 : ℚ) : ℝ)) ≤ ((61 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_911 : sigmaPower (911 : Fin 1536) ≤ ((1400740974299 / 4398046511104 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_912 : sigmaFactor (912 : Fin 1536) ≤ ((63 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-51068193 / 1785856 : ℚ) : ℝ) - Real.exp ((-3196633 / 111616 : ℚ) : ℝ)) ≤ ((63 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_912 : sigmaPower (912 : Fin 1536) ≤ ((89521093510423 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_913 : sigmaFactor (913 : Fin 1536) ≤ ((65 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-1224150675 / 42852352 : ℚ) : ℝ) - Real.exp ((-2452041515 / 85704704 : ℚ) : ℝ)) ≤ ((65 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_913 : sigmaPower (913 : Fin 1536) ≤ ((89394716365635 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_914 : sigmaFactor (914 : Fin 1536) ≤ ((67 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-1222665433 / 42844160 : ℚ) : ℝ) - Real.exp ((-612267579 / 21422080 : ℚ) : ℝ)) ≤ ((67 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_914 : sigmaPower (914 : Fin 1536) ≤ ((22317072723267 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_915 : sigmaFactor (915 : Fin 1536) ≤ ((69 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-203530151 / 7139328 : ℚ) : ℝ) - Real.exp ((-815366849 / 28557312 : ℚ) : ℝ)) ≤ ((69 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_915 : sigmaPower (915 : Fin 1536) ≤ ((89141817064993 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_916 : sigmaFactor (916 : Fin 1536) ≤ ((71 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-609848547 / 21413888 : ℚ) : ℝ) - Real.exp ((-152695763 / 5353472 : ℚ) : ℝ)) ≤ ((71 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_916 : sigmaPower (916 : Fin 1536) ≤ ((2781727964177 / 8796093022208 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_917 : sigmaFactor (917 : Fin 1536) ≤ ((73 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-1218213997 / 42819584 : ℚ) : ℝ) - Real.exp ((-2440165299 / 85639168 : ℚ) : ℝ)) ≤ ((73 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_917 : sigmaPower (917 : Fin 1536) ≤ ((44444362115655 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_918 : sigmaFactor (918 : Fin 1536) ≤ ((75 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-405577205 / 14270464 : ℚ) : ℝ) - Real.exp ((-203099985 / 7135232 : ℚ) : ℝ)) ≤ ((75 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_918 : sigmaPower (918 : Fin 1536) ≤ ((44381052585071 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_919 : sigmaFactor (919 : Fin 1536) ≤ ((77 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-27619317 / 972800 : ℚ) : ℝ) - Real.exp ((-221294161 / 7782400 : ℚ) : ℝ)) ≤ ((77 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_919 : sigmaPower (919 : Fin 1536) ≤ ((22158859410587 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_920 : sigmaFactor (920 : Fin 1536) ≤ ((5 / 17592186044416 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-303442249 / 10698752 : ℚ) : ℝ) - Real.exp ((-37988643 / 1337344 : ℚ) : ℝ)) ≤ ((5 / 17592186044416 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_920 : sigmaPower (920 : Fin 1536) ≤ ((44254360810047 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_921 : sigmaFactor (921 : Fin 1536) ≤ ((41 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-404096253 / 14262272 : ℚ) : ℝ) - Real.exp ((-809437321 / 28524544 : ℚ) : ℝ)) ≤ ((41 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_921 : sigmaPower (921 : Fin 1536) ≤ ((88381957075527 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_922 : sigmaFactor (922 : Fin 1536) ≤ ((21 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-1210809237 / 42778624 : ℚ) : ℝ) - Real.exp ((-606338051 / 21389312 : ℚ) : ℝ)) ≤ ((21 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_922 : sigmaPower (922 : Fin 1536) ≤ ((44127571990385 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_923 : sigmaFactor (923 : Fin 1536) ≤ ((87 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-604665215 / 21385216 : ℚ) : ℝ) - Real.exp ((-2422393875 / 85540864 : ℚ) : ℝ)) ≤ ((87 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_923 : sigmaPower (923 : Fin 1536) ≤ ((88128282307927 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_924 : sigmaFactor (924 : Fin 1536) ≤ ((89 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-201308723 / 7127040 : ℚ) : ℝ) - Real.exp ((-50404937 / 1781760 : ℚ) : ℝ)) ≤ ((89 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_924 : sigmaPower (924 : Fin 1536) ≤ ((88001372029079 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_925 : sigmaFactor (925 : Fin 1536) ≤ ((23 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-70963233 / 2514944 : ℚ) : ℝ) - Real.exp ((-142145971 / 5029888 : ℚ) : ℝ)) ≤ ((23 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_925 : sigmaPower (925 : Fin 1536) ≤ ((43937206558143 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_926 : sigmaFactor (926 : Fin 1536) ≤ ((95 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-1204898299 / 42745856 : ℚ) : ℝ) - Real.exp ((-603381867 / 21372928 : ℚ) : ℝ)) ≤ ((95 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_926 : sigmaPower (926 : Fin 1536) ≤ ((87747405541587 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_927 : sigmaFactor (927 : Fin 1536) ≤ ((97 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-25071299 / 890368 : ℚ) : ℝ) - Real.exp ((-803524953 / 28491776 : ℚ) : ℝ)) ≤ ((97 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_927 : sigmaPower (927 : Fin 1536) ≤ ((10952543659625 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_928 : sigmaFactor (928 : Fin 1536) ≤ ((25 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-75121695 / 2670592 : ℚ) : ℝ) - Real.exp ((-2351195 / 83456 : ℚ) : ℝ)) ≤ ((25 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_928 : sigmaPower (928 : Fin 1536) ≤ ((87493244294519 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_929 : sigmaFactor (929 : Fin 1536) ≤ ((103 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-1200472603 / 42721280 : ℚ) : ℝ) - Real.exp ((-2404673931 / 85442560 : ℚ) : ℝ)) ≤ ((103 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_929 : sigmaPower (929 : Fin 1536) ≤ ((10920761320765 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_930 : sigmaFactor (930 : Fin 1536) ≤ ((53 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-36333297 / 1294336 : ℚ) : ℝ) - Real.exp ((-18194891 / 647168 : ℚ) : ℝ)) ≤ ((53 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_930 : sigmaPower (930 : Fin 1536) ≤ ((21809722015939 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_931 : sigmaFactor (931 : Fin 1536) ≤ ((109 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-598762857 / 21352448 : ℚ) : ℝ) - Real.exp ((-2398778723 / 85409792 : ℚ) : ℝ)) ≤ ((109 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_931 : sigmaPower (931 : Fin 1536) ≤ ((87111636759357 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_932 : sigmaFactor (932 : Fin 1536) ≤ ((113 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-598026671 / 21348352 : ℚ) : ℝ) - Real.exp ((-149739579 / 5337088 : ℚ) : ℝ)) ≤ ((113 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_932 : sigmaPower (932 : Fin 1536) ≤ ((43492168312417 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_933 : sigmaFactor (933 : Fin 1536) ≤ ((29 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-398193895 / 14229504 : ℚ) : ℝ) - Real.exp ((-797629745 / 28459008 : ℚ) : ℝ)) ≤ ((29 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_933 : sigmaPower (933 : Fin 1536) ≤ ((43428493816037 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_934 : sigmaFactor (934 : Fin 1536) ≤ ((119 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-1193110743 / 42680320 : ℚ) : ℝ) - Real.exp ((-597486659 / 21340160 : ℚ) : ℝ)) ≤ ((119 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_934 : sigmaPower (934 : Fin 1536) ≤ ((86729589752945 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_935 : sigmaFactor (935 : Fin 1536) ≤ ((123 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-297910129 / 10668032 : ℚ) : ℝ) - Real.exp ((-2387005467 / 85344256 : ℚ) : ℝ)) ≤ ((123 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_935 : sigmaPower (935 : Fin 1536) ≤ ((86602142959291 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_936 : sigmaFactor (936 : Fin 1536) ≤ ((63 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-99180917 / 3555328 : ℚ) : ℝ) - Real.exp ((-12417009 / 444416 : ℚ) : ℝ)) ≤ ((63 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_936 : sigmaPower (936 : Fin 1536) ≤ ((10809330902867 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_937 : sigmaFactor (937 : Fin 1536) ≤ ((65 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-1188702207 / 42655744 : ℚ) : ℝ) - Real.exp ((-2381127419 / 85311488 : ℚ) : ℝ)) ≤ ((65 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_937 : sigmaPower (937 : Fin 1536) ≤ ((43173551257841 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_938 : sigmaFactor (938 : Fin 1536) ≤ ((67 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-1187234125 / 42647552 : ℚ) : ℝ) - Real.exp ((-594547635 / 21323776 : ℚ) : ℝ)) ≤ ((67 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_938 : sigmaPower (938 : Fin 1536) ≤ ((86219508809309 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_939 : sigmaFactor (939 : Fin 1536) ≤ ((69 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-197627793 / 7106560 : ℚ) : ℝ) - Real.exp ((-791751697 / 28426240 : ℚ) : ℝ)) ≤ ((69 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_939 : sigmaPower (939 : Fin 1536) ≤ ((86091866075575 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_940 : sigmaFactor (940 : Fin 1536) ≤ ((71 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-592150053 / 21315584 : ℚ) : ℝ) - Real.exp ((-148270067 / 5328896 : ℚ) : ℝ)) ≤ ((71 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_940 : sigmaPower (940 : Fin 1536) ≤ ((85964174286217 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_941 : sigmaFactor (941 : Fin 1536) ≤ ((73 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-9775489 / 352256 : ℚ) : ℝ) - Real.exp ((-19581723 / 704512 : ℚ) : ℝ)) ≤ ((73 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_941 : sigmaPower (941 : Fin 1536) ≤ ((42918216706475 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_942 : sigmaFactor (942 : Fin 1536) ≤ ((75 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-23164097 / 835584 : ℚ) : ℝ) - Real.exp ((-11600281 / 417792 : ℚ) : ℝ)) ≤ ((75 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_942 : sigmaPower (942 : Fin 1536) ≤ ((85708643427467 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_943 : sigmaFactor (943 : Fin 1536) ≤ ((155 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-147488055 / 5325824 : ℚ) : ℝ) - Real.exp ((-2363527595 / 85213184 : ℚ) : ℝ)) ≤ ((155 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_943 : sigmaPower (943 : Fin 1536) ≤ ((85580804301439 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_944 : sigmaFactor (944 : Fin 1536) ≤ ((159 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-147305081 / 5324800 : ℚ) : ℝ) - Real.exp ((-9221091 / 332800 : ℚ) : ℝ)) ≤ ((159 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_944 : sigmaPower (944 : Fin 1536) ≤ ((42726458003259 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_945 : sigmaFactor (945 : Fin 1536) ≤ ((41 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-392325857 / 14196736 : ℚ) : ℝ) - Real.exp ((-785890809 / 28393472 : ℚ) : ℝ)) ≤ ((41 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_945 : sigmaPower (945 : Fin 1536) ≤ ((85324978514329 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_946 : sigmaFactor (946 : Fin 1536) ≤ ((169 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-1175515209 / 42582016 : ℚ) : ℝ) - Real.exp ((-588686747 / 21291008 : ℚ) : ℝ)) ≤ ((169 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_946 : sigmaPower (946 : Fin 1536) ≤ ((332800749205 / 1099511627776 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_947 : sigmaFactor (947 : Fin 1536) ≤ ((87 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-587026781 / 21286912 : ℚ) : ℝ) - Real.exp ((-2351822979 / 85147648 : ℚ) : ℝ)) ≤ ((87 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_947 : sigmaPower (947 : Fin 1536) ≤ ((42534477912277 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_948 : sigmaFactor (948 : Fin 1536) ≤ ((179 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-195432105 / 7094272 : ℚ) : ℝ) - Real.exp ((-48935425 / 1773568 : ℚ) : ℝ)) ≤ ((179 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_948 : sigmaPower (948 : Fin 1536) ≤ ((42470435285057 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_949 : sigmaFactor (949 : Fin 1536) ≤ ((23 / 35184372088832 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-1171132413 / 42557440 : ℚ) : ℝ) - Real.exp ((-2345979251 / 85114880 : ℚ) : ℝ)) ≤ ((23 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_949 : sigmaPower (949 : Fin 1536) ≤ ((21203184001175 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_950 : sigmaFactor (950 : Fin 1536) ≤ ((95 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-1169672911 / 42549248 : ℚ) : ℝ) - Real.exp ((-585764883 / 21274624 : ℚ) : ℝ)) ≤ ((95 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_950 : sigmaPower (950 : Fin 1536) ≤ ((84684552099831 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_951 : sigmaFactor (951 : Fin 1536) ≤ ((195 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-97351177 / 3545088 : ℚ) : ℝ) - Real.exp ((-780047081 / 28360704 : ℚ) : ℝ)) ≤ ((195 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_951 : sigmaPower (951 : Fin 1536) ≤ ((84556318827003 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_952 : sigmaFactor (952 : Fin 1536) ≤ ((201 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-26517183 / 966656 : ℚ) : ℝ) - Real.exp ((-3319921 / 120832 : ℚ) : ℝ)) ≤ ((201 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_952 : sigmaPower (952 : Fin 1536) ≤ ((84428036157691 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_953 : sigmaFactor (953 : Fin 1536) ≤ ((207 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-1165298695 / 42524672 : ℚ) : ℝ) - Real.exp ((-2334308955 / 85049344 : ℚ) : ℝ)) ≤ ((207 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_953 : sigmaPower (953 : Fin 1536) ≤ ((84299704063347 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_954 : sigmaFactor (954 : Fin 1536) ≤ ((213 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-387947351 / 14172160 : ℚ) : ℝ) - Real.exp ((-194282913 / 7086080 : ℚ) : ℝ)) ≤ ((213 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_954 : sigmaPower (954 : Fin 1536) ≤ ((84171322515403 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_955 : sigmaFactor (955 : Fin 1536) ≤ ((219 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-581193063 / 21254144 : ℚ) : ℝ) - Real.exp ((-2328482387 / 85016576 : ℚ) : ℝ)) ≤ ((219 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_955 : sigmaPower (955 : Fin 1536) ≤ ((42021445742633 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_956 : sigmaFactor (956 : Fin 1536) ≤ ((225 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-580465457 / 21250048 : ℚ) : ℝ) - Real.exp ((-145348203 / 5312512 : ℚ) : ℝ)) ≤ ((225 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_956 : sigmaPower (956 : Fin 1536) ≤ ((20978602736081 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_957 : sigmaFactor (957 : Fin 1536) ≤ ((29 / 35184372088832 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-386492139 / 14163968 : ℚ) : ℝ) - Real.exp ((-774220513 / 28327936 : ℚ) : ℝ)) ≤ ((29 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_957 : sigmaPower (957 : Fin 1536) ≤ ((20946470215985 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_958 : sigmaFactor (958 : Fin 1536) ≤ ((239 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-1158022635 / 42483712 : ℚ) : ℝ) - Real.exp ((-579938315 / 21241856 : ℚ) : ℝ)) ≤ ((239 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_958 : sigmaPower (958 : Fin 1536) ≤ ((83657301215457 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_959 : sigmaFactor (959 : Fin 1536) ≤ ((123 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-2126047 / 78080 : ℚ) : ℝ) - Real.exp ((-136285083 / 4997120 : ℚ) : ℝ)) ≤ ((123 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_959 : sigmaPower (959 : Fin 1536) ≤ ((20882167992549 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_960 : sigmaFactor (960 : Fin 1536) ≤ ((253 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-12032471 / 442368 : ℚ) : ℝ) - Real.exp ((-188309 / 6912 : ℚ) : ℝ)) ≤ ((253 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_960 : sigmaPower (960 : Fin 1536) ≤ ((41699996549727 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_961 : sigmaFactor (961 : Fin 1536) ≤ ((261 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-1153665579 / 42459136 : ℚ) : ℝ) - Real.exp ((-2311037003 / 84918272 : ℚ) : ℝ)) ≤ ((261 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_961 : sigmaPower (961 : Fin 1536) ≤ ((20817816143627 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_962 : sigmaFactor (962 : Fin 1536) ≤ ((67 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-1152214657 / 42450944 : ℚ) : ℝ) - Real.exp ((-577033611 / 21225472 : ℚ) : ℝ)) ≤ ((67 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_962 : sigmaPower (962 : Fin 1536) ≤ ((83142486366611 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_963 : sigmaFactor (963 : Fin 1536) ≤ ((69 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-17435825 / 643072 : ℚ) : ℝ) - Real.exp ((-69855555 / 2572288 : ℚ) : ℝ)) ≤ ((69 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_963 : sigmaPower (963 : Fin 1536) ≤ ((20753414611749 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_964 : sigmaFactor (964 : Fin 1536) ≤ ((71 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-574657479 / 21217280 : ℚ) : ℝ) - Real.exp ((-143895851 / 5304320 : ℚ) : ℝ)) ≤ ((71 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_964 : sigmaPower (964 : Fin 1536) ≤ ((82884780786871 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_965 : sigmaFactor (965 : Fin 1536) ≤ ((73 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-1147866181 / 42426368 : ℚ) : ℝ) - Real.exp ((-2299435347 / 84852736 : ℚ) : ℝ)) ≤ ((73 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_965 : sigmaPower (965 : Fin 1536) ≤ ((82755853357423 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_966 : sigmaFactor (966 : Fin 1536) ≤ ((301 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-382139373 / 14139392 : ℚ) : ℝ) - Real.exp ((-191378209 / 7069696 : ℚ) : ℝ)) ≤ ((301 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_966 : sigmaPower (966 : Fin 1536) ≤ ((41313438064909 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_967 : sigmaFactor (967 : Fin 1536) ≤ ((155 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-286242693 / 10602496 : ℚ) : ℝ) - Real.exp ((-2293643099 / 84819968 : ℚ) : ℝ)) ≤ ((155 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_967 : sigmaPower (967 : Fin 1536) ≤ ((82497849075199 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_968 : sigmaFactor (968 : Fin 1536) ≤ ((319 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-285881035 / 10600448 : ℚ) : ℝ) - Real.exp ((-35792955 / 1325056 : ℚ) : ℝ)) ≤ ((319 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_968 : sigmaPower (968 : Fin 1536) ≤ ((82368772164685 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_969 : sigmaFactor (969 : Fin 1536) ≤ ((41 / 35184372088832 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-380692741 / 14131200 : ℚ) : ℝ) - Real.exp ((-762618857 / 28262400 : ℚ) : ℝ)) ≤ ((41 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_969 : sigmaPower (969 : Fin 1536) ≤ ((82239645369375 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_970 : sigmaFactor (970 : Fin 1536) ≤ ((169 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-1140633021 / 42385408 : ℚ) : ℝ) - Real.exp ((-571241363 / 21192704 : ℚ) : ℝ)) ≤ ((169 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_970 : sigmaPower (970 : Fin 1536) ≤ ((10263808582543 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_971 : sigmaFactor (971 : Fin 1536) ≤ ((87 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-569594267 / 21188608 : ℚ) : ℝ) - Real.exp ((-2282075763 / 84754432 : ℚ) : ℝ)) ≤ ((87 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_971 : sigmaPower (971 : Fin 1536) ≤ ((40990621004323 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_972 : sigmaFactor (972 : Fin 1536) ≤ ((179 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-189624127 / 7061504 : ℚ) : ℝ) - Real.exp ((-47483073 / 1765376 : ℚ) : ℝ)) ≤ ((179 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_972 : sigmaPower (972 : Fin 1536) ≤ ((81851965385311 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_973 : sigmaFactor (973 : Fin 1536) ≤ ((23 / 17592186044416 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-1136301705 / 42360832 : ℚ) : ℝ) - Real.exp ((-2276300675 / 84721664 : ℚ) : ℝ)) ≤ ((23 / 17592186044416 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_973 : sigmaPower (973 : Fin 1536) ≤ ((81722638761349 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_974 : sigmaFactor (974 : Fin 1536) ≤ ((379 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-103169033 / 3850240 : ℚ) : ℝ) - Real.exp ((-51668529 / 1925120 : ℚ) : ℝ)) ≤ ((379 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_974 : sigmaPower (974 : Fin 1536) ≤ ((2549789440867 / 8796093022208 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_975 : sigmaFactor (975 : Fin 1536) ≤ ((195 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-47225739 / 1764352 : ℚ) : ℝ) - Real.exp ((-756843769 / 28229632 : ℚ) : ℝ)) ≤ ((195 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_975 : sigmaPower (975 : Fin 1536) ≤ ((40731917697731 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_976 : sigmaFactor (976 : Fin 1536) ≤ ((201 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-8323359 / 311296 : ℚ) : ℝ) - Real.exp ((-521059 / 19456 : ℚ) : ℝ)) ≤ ((201 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_976 : sigmaPower (976 : Fin 1536) ≤ ((81334358595443 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_977 : sigmaFactor (977 : Fin 1536) ≤ ((413 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-1130536627 / 42328064 : ℚ) : ℝ) - Real.exp ((-2264767659 / 84656128 : ℚ) : ℝ)) ≤ ((413 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_977 : sigmaPower (977 : Fin 1536) ≤ ((81204831678605 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_978 : sigmaFactor (978 : Fin 1536) ≤ ((425 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-376365715 / 14106624 : ℚ) : ℝ) - Real.exp ((-188490665 / 7053312 : ℚ) : ℝ)) ≤ ((425 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_978 : sigmaPower (978 : Fin 1536) ≤ ((40537627307923 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_979 : sigmaFactor (979 : Fin 1536) ≤ ((219 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-563829189 / 21155840 : ℚ) : ℝ) - Real.exp ((-2259009731 / 84623360 : ℚ) : ℝ)) ≤ ((219 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_979 : sigmaPower (979 : Fin 1536) ≤ ((80945627378037 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_980 : sigmaFactor (980 : Fin 1536) ≤ ((451 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-563110163 / 21151744 : ℚ) : ℝ) - Real.exp ((-141008307 / 5287936 : ℚ) : ℝ)) ≤ ((451 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_980 : sigmaPower (980 : Fin 1536) ≤ ((2525498435501 / 8796093022208 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_981 : sigmaFactor (981 : Fin 1536) ≤ ((29 / 17592186044416 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-374927663 / 14098432 : ℚ) : ℝ) - Real.exp ((-751085841 / 28196864 : ℚ) : ℝ)) ≤ ((29 / 17592186044416 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_981 : sigmaPower (981 : Fin 1536) ≤ ((80686222260657 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_982 : sigmaFactor (982 : Fin 1536) ≤ ((477 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-1123346367 / 42287104 : ℚ) : ℝ) - Real.exp ((-562595891 / 21143552 : ℚ) : ℝ)) ≤ ((477 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_982 : sigmaPower (982 : Fin 1536) ≤ ((2517388885085 / 8796093022208 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_983 : sigmaFactor (983 : Fin 1536) ≤ ((491 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-280477615 / 10569728 : ℚ) : ℝ) - Real.exp ((-2247511035 / 84557824 : ℚ) : ℝ)) ≤ ((491 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_983 : sigmaPower (983 : Fin 1536) ≤ ((40213308046501 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_984 : sigmaFactor (984 : Fin 1536) ≤ ((253 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-93372939 / 3522560 : ℚ) : ℝ) - Real.exp ((-11690833 / 440320 : ℚ) : ℝ)) ≤ ((253 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_984 : sigmaPower (984 : Fin 1536) ≤ ((80296737542265 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_985 : sigmaFactor (985 : Fin 1536) ≤ ((65 / 35184372088832 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-101730981 / 3842048 : ℚ) : ℝ) - Real.exp ((-203797297 / 7684096 : ℚ) : ℝ)) ≤ ((65 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_985 : sigmaPower (985 : Fin 1536) ≤ ((80166808641247 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_986 : sigmaFactor (986 : Fin 1536) ≤ ((67 / 35184372088832 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-1117607029 / 42254336 : ℚ) : ℝ) - Real.exp ((-559725507 / 21127168 : ℚ) : ℝ)) ≤ ((67 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_986 : sigmaPower (986 : Fin 1536) ≤ ((80036829360663 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_987 : sigmaFactor (987 : Fin 1536) ≤ ((551 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-186028997 / 7041024 : ℚ) : ℝ) - Real.exp ((-745345073 / 28164096 : ℚ) : ℝ)) ≤ ((551 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_987 : sigmaPower (987 : Fin 1536) ≤ ((79906799671205 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_988 : sigmaFactor (988 : Fin 1536) ≤ ((567 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-557370825 / 21118976 : ℚ) : ℝ) - Real.exp ((-139573115 / 5279744 : ℚ) : ℝ)) ≤ ((567 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_988 : sigmaPower (988 : Fin 1536) ≤ ((79776719543543 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_989 : sigmaFactor (989 : Fin 1536) ≤ ((73 / 35184372088832 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-1113310033 / 42229760 : ℚ) : ℝ) - Real.exp ((-2230305891 / 84459520 : ℚ) : ℝ)) ≤ ((73 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_989 : sigmaPower (989 : Fin 1536) ≤ ((19911647237081 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_990 : sigmaFactor (990 : Fin 1536) ≤ ((601 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-370626377 / 14073856 : ℚ) : ℝ) - Real.exp ((-185620281 / 7036928 : ℚ) : ℝ)) ≤ ((601 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_990 : sigmaPower (990 : Fin 1536) ≤ ((79516407856173 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_991 : sigmaFactor (991 : Fin 1536) ≤ ((309 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-69403059 / 2638336 : ℚ) : ℝ) - Real.exp ((-2224582283 / 84426752 : ℚ) : ℝ)) ≤ ((309 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_991 : sigmaPower (991 : Fin 1536) ≤ ((79386176237691 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_992 : sigmaFactor (992 : Fin 1536) ≤ ((159 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-69313717 / 2637824 : ℚ) : ℝ) - Real.exp ((-2169651 / 82432 : ℚ) : ℝ)) ≤ ((159 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_992 : sigmaPower (992 : Fin 1536) ≤ ((2476746689483 / 8796093022208 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_993 : sigmaFactor (993 : Fin 1536) ≤ ((655 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-21717465 / 827392 : ℚ) : ℝ) - Real.exp ((-43507145 / 1654784 : ℚ) : ℝ)) ≤ ((655 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_993 : sigmaPower (993 : Fin 1536) ≤ ((79125561304025 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_994 : sigmaFactor (994 : Fin 1536) ≤ ((337 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-1106162673 / 42188800 : ℚ) : ℝ) - Real.exp ((-554001899 / 21094400 : ℚ) : ℝ)) ≤ ((337 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_994 : sigmaPower (994 : Fin 1536) ≤ ((39497588964965 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_995 : sigmaFactor (995 : Fin 1536) ≤ ((347 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-552367673 / 21090304 : ℚ) : ℝ) - Real.exp ((-2213152227 / 84361216 : ℚ) : ℝ)) ≤ ((347 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_995 : sigmaPower (995 : Fin 1536) ≤ ((308065405905 / 1099511627776 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_996 : sigmaFactor (996 : Fin 1536) ≤ ((357 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-16716799 / 638976 : ℚ) : ℝ) - Real.exp ((-4186171 / 159744 : ℚ) : ℝ)) ≤ ((357 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_996 : sigmaPower (996 : Fin 1536) ≤ ((19683564804941 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_997 : sigmaFactor (997 : Fin 1536) ≤ ((735 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-1101882837 / 42164224 : ℚ) : ℝ) - Real.exp ((-2207445779 / 84328448 : ℚ) : ℝ)) ≤ ((735 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_997 : sigmaPower (997 : Fin 1536) ≤ ((39301861912323 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_998 : sigmaFactor (998 : Fin 1536) ≤ ((189 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-1100457655 / 42156032 : ℚ) : ℝ) - Real.exp ((-551148675 / 21078016 : ℚ) : ℝ)) ≤ ((189 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_998 : sigmaPower (998 : Fin 1536) ≤ ((39236568848383 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_999 : sigmaFactor (999 : Fin 1536) ≤ ((389 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-91586099 / 3512320 : ℚ) : ℝ) - Real.exp ((-733915017 / 28098560 : ℚ) : ℝ)) ≤ ((389 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_999 : sigmaPower (999 : Fin 1536) ≤ ((78342500806543 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1000 : sigmaFactor (1000 : Fin 1536) ≤ ((801 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-274402359 / 10534912 : ℚ) : ℝ) - Real.exp ((-34357763 / 1316864 : ℚ) : ℝ)) ≤ ((801 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1000 : sigmaPower (1000 : Fin 1536) ≤ ((78211813124371 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1001 : sigmaFactor (1001 : Fin 1536) ≤ ((103 / 35184372088832 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-1096186399 / 42131456 : ℚ) : ℝ) - Real.exp ((-2196050043 / 84262912 : ℚ) : ℝ)) ≤ ((103 / 35184372088832 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1001 : sigmaPower (1001 : Fin 1536) ≤ ((4880067163789 / 17592186044416 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1002 : sigmaFactor (1002 : Fin 1536) ≤ ((53 / 17592186044416 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-364921359 / 14041088 : ℚ) : ℝ) - Real.exp ((-182767057 / 7020544 : ℚ) : ℝ)) ≤ ((53 / 17592186044416 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1002 : sigmaPower (1002 : Fin 1536) ≤ ((77950285265651 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1003 : sigmaFactor (1003 : Fin 1536) ≤ ((873 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-546671235 / 21057536 : ℚ) : ℝ) - Real.exp ((-2190360755 / 84230144 : ℚ) : ℝ)) ≤ ((873 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1003 : sigmaPower (1003 : Fin 1536) ≤ ((77819445029777 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1004 : sigmaFactor (1004 : Fin 1536) ≤ ((449 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-545960789 / 21053440 : ℚ) : ℝ) - Real.exp ((-136719891 / 5263360 : ℚ) : ℝ)) ≤ ((449 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1004 : sigmaPower (1004 : Fin 1536) ≤ ((77688553883305 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1005 : sigmaFactor (1005 : Fin 1536) ≤ ((231 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-363500467 / 14032896 : ℚ) : ℝ) - Real.exp ((-728225729 / 28065792 : ℚ) : ℝ)) ≤ ((231 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1005 : sigmaPower (1005 : Fin 1536) ≤ ((77557611796515 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1006 : sigmaFactor (1006 : Fin 1536) ≤ ((951 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-1089081939 / 42090496 : ℚ) : ℝ) - Real.exp ((-545459387 / 21045248 : ℚ) : ℝ)) ≤ ((951 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1006 : sigmaPower (1006 : Fin 1536) ≤ ((77426618739665 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1007 : sigmaFactor (1007 : Fin 1536) ≤ ((979 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-12359809 / 478208 : ℚ) : ℝ) - Real.exp ((-198090849 / 7651328 : ℚ) : ℝ)) ≤ ((979 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1007 : sigmaPower (1007 : Fin 1536) ≤ ((38647787341493 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1008 : sigmaFactor (1008 : Fin 1536) ≤ ((1007 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-45260215 / 1753088 : ℚ) : ℝ) - Real.exp ((-2833545 / 109568 : ℚ) : ℝ)) ≤ ((1007 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1008 : sigmaPower (1008 : Fin 1536) ≤ ((77164479596691 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1009 : sigmaFactor (1009 : Fin 1536) ≤ ((1037 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-1084827843 / 42065920 : ℚ) : ℝ) - Real.exp ((-2173327211 / 84131840 : ℚ) : ℝ)) ≤ ((1037 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1009 : sigmaPower (1009 : Fin 1536) ≤ ((38516666725483 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1010 : sigmaFactor (1010 : Fin 1536) ≤ ((1067 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-63730073 / 2473984 : ℚ) : ℝ) - Real.exp ((-31919019 / 1236992 : ℚ) : ℝ)) ≤ ((1067 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1010 : sigmaPower (1010 : Fin 1536) ≤ ((76902136215975 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1011 : sigmaFactor (1011 : Fin 1536) ≤ ((549 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-180332559 / 7008256 : ℚ) : ℝ) - Real.exp ((-722553601 / 28033024 : ℚ) : ℝ)) ≤ ((549 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1011 : sigmaPower (1011 : Fin 1536) ≤ ((76770887861859 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1012 : sigmaFactor (1012 : Fin 1536) ≤ ((565 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-540290091 / 21020672 : ℚ) : ℝ) - Real.exp ((-135301859 / 5255168 : ℚ) : ℝ)) ≤ ((565 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1012 : sigmaPower (1012 : Fin 1536) ≤ ((76639588358735 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1013 : sigmaFactor (1013 : Fin 1536) ≤ ((581 / 140737488355328 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-1079165725 / 42033152 : ℚ) : ℝ) - Real.exp ((-2162000115 / 84066304 : ℚ) : ℝ)) ≤ ((581 / 140737488355328 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1013 : sigmaPower (1013 : Fin 1536) ≤ ((76508237676697 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1014 : sigmaFactor (1014 : Fin 1536) ≤ ((299 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-359250661 / 14008320 : ℚ) : ℝ) - Real.exp ((-179930993 / 7004160 : ℚ) : ℝ)) ≤ ((299 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1014 : sigmaPower (1014 : Fin 1536) ≤ ((9547104473227 / 35184372088832 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1015 : sigmaFactor (1015 : Fin 1536) ≤ ((1231 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-269084739 / 10504192 : ℚ) : ℝ) - Real.exp ((-2156345147 / 84033536 : ℚ) : ℝ)) ≤ ((1231 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1015 : sigmaPower (1015 : Fin 1536) ≤ ((19061345664035 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1016 : sigmaFactor (1016 : Fin 1536) ≤ ((1267 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-268731661 / 10502144 : ℚ) : ℝ) - Real.exp ((-33648747 / 1312768 : ℚ) : ℝ)) ≤ ((1267 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1016 : sigmaPower (1016 : Fin 1536) ≤ ((19028469564423 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1017 : sigmaFactor (1017 : Fin 1536) ≤ ((1303 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-357838349 / 14000128 : ℚ) : ℝ) - Real.exp ((-716898633 / 28000256 : ℚ) : ℝ)) ≤ ((1303 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1017 : sigmaPower (1017 : Fin 1536) ≤ ((37991161280237 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1018 : sigmaFactor (1018 : Fin 1536) ≤ ((1341 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-97464015 / 3817472 : ℚ) : ℝ) - Real.exp ((-48815305 / 1908736 : ℚ) : ℝ)) ≤ ((1341 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1018 : sigmaPower (1018 : Fin 1536) ≤ ((75850715534463 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1019 : sigmaFactor (1019 : Fin 1536) ≤ ((345 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-535346999 / 20992000 : ℚ) : ℝ) - Real.exp ((-2145052371 / 83968000 : ℚ) : ℝ)) ≤ ((345 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1019 : sigmaPower (1019 : Fin 1536) ≤ ((18929764287403 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1020 : sigmaFactor (1020 : Fin 1536) ≤ ((355 / 70368744177664 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-178214091 / 6995968 : ℚ) : ℝ) - Real.exp ((-44629849 / 1748992 : ℚ) : ℝ)) ≤ ((355 / 70368744177664 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1020 : sigmaPower (1020 : Fin 1536) ≤ ((18896836843963 / 70368744177664 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1021 : sigmaFactor (1021 : Fin 1536) ≤ ((1461 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-1067875809 / 41967616 : ℚ) : ℝ) - Real.exp ((-2139414563 / 83935232 : ℚ) : ℝ)) ≤ ((1461 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1021 : sigmaPower (1021 : Fin 1536) ≤ ((37727793091545 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1022 : sigmaFactor (1022 : Fin 1536) ≤ ((47 / 8796093022208 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-1066467787 / 41959424 : ℚ) : ℝ) - Real.exp ((-534149451 / 20979712 : ℚ) : ℝ)) ≤ ((47 / 8796093022208 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1022 : sigmaPower (1022 : Fin 1536) ≤ ((75323773541209 / 281474976710656 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

theorem sigma_factor_upper_1023 : sigmaFactor (1023 : Fin 1536) ≤ ((1547 / 281474976710656 : ℚ) : ℝ) := by
  have h : ((683 / 50 : ℚ) : ℝ) * (Real.exp ((-2773595 / 109248 : ℚ) : ℝ) - Real.exp ((-711260825 / 27967488 : ℚ) : ℝ)) ≤ ((1547 / 281474976710656 : ℚ) : ℝ) := by
    dyadic_interval [prec := 96]
  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢
  exact h
theorem sigma_power_upper_1023 : sigmaPower (1023 : Fin 1536) ≤ ((37595954710035 / 140737488355328 : ℚ) : ℝ) := by
  norm_num [sigmaPower, exponent, sigmaLo, shiftP]

end LegendreK6.M2Pilot.Enclosures.Sigma007
