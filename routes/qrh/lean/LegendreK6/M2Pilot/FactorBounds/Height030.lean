import LegendreK6.M2Pilot.Enclosures.Height030
import LegendreK6.M2PilotIntegerData

/-! Join checked analytic enclosures to the exact dyadic witness table. -/
namespace LegendreK6.M2Pilot.FactorBounds.Height030
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem bounds (i : Fin 988) (hlo : 960 ≤ i.val) (hhi : i.val < 988) :
    heightFactor i ≤ heightDyadicFactor i ∧ heightPower i ≤ heightDyadicPower i := by
  interval_cases hi : i.val
  · have heq : i = (960 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height030.height_factor_upper_960.trans
      change ((16533429 / 281474976710656 : ℚ) : ℝ) ≤ ((16533429 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height030.height_power_upper_960.trans
      change ((4340296471271917 / 281474976710656 : ℚ) : ℝ) ≤ ((4340296471271917 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (961 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height030.height_factor_upper_961.trans
      change ((8061739 / 140737488355328 : ℚ) : ℝ) ≤ ((16123478 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height030.height_power_upper_961.trans
      change ((1086198738721375 / 70368744177664 : ℚ) : ℝ) ≤ ((4344794954885500 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (962 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height030.height_factor_upper_962.trans
      change ((15723727 / 281474976710656 : ℚ) : ℝ) ≤ ((15723727 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height030.height_power_upper_962.trans
      change ((4349293402673471 / 281474976710656 : ℚ) : ℝ) ≤ ((4349293402673471 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (963 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height030.height_factor_upper_963.trans
      change ((15333923 / 281474976710656 : ℚ) : ℝ) ≤ ((15333923 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height030.height_power_upper_963.trans
      change ((4353791814661377 / 281474976710656 : ℚ) : ℝ) ≤ ((4353791814661377 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (964 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height030.height_factor_upper_964.trans
      change ((14953819 / 281474976710656 : ℚ) : ℝ) ≤ ((14953819 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height030.height_power_upper_964.trans
      change ((4358290190874741 / 281474976710656 : ℚ) : ℝ) ≤ ((4358290190874741 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (965 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height030.height_factor_upper_965.trans
      change ((14583173 / 281474976710656 : ℚ) : ℝ) ≤ ((14583173 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height030.height_power_upper_965.trans
      change ((4362788531339057 / 281474976710656 : ℚ) : ℝ) ≤ ((4362788531339057 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (966 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height030.height_factor_upper_966.trans
      change ((14221751 / 281474976710656 : ℚ) : ℝ) ≤ ((14221751 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height030.height_power_upper_966.trans
      change ((4367286836079791 / 281474976710656 : ℚ) : ℝ) ≤ ((4367286836079791 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (967 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height030.height_factor_upper_967.trans
      change ((6934661 / 140737488355328 : ℚ) : ℝ) ≤ ((13869322 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height030.height_power_upper_967.trans
      change ((4371785105122383 / 281474976710656 : ℚ) : ℝ) ≤ ((4371785105122383 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (968 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height030.height_factor_upper_968.trans
      change ((6762831 / 140737488355328 : ℚ) : ℝ) ≤ ((13525662 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height030.height_power_upper_968.trans
      change ((2188141669246123 / 140737488355328 : ℚ) : ℝ) ≤ ((4376283338492246 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (969 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height030.height_factor_upper_969.trans
      change ((13190555 / 281474976710656 : ℚ) : ℝ) ≤ ((13190555 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height030.height_power_upper_969.trans
      change ((1095195384053691 / 70368744177664 : ℚ) : ℝ) ≤ ((4380781536214764 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (970 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height030.height_factor_upper_970.trans
      change ((12863787 / 281474976710656 : ℚ) : ℝ) ≤ ((12863787 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height030.height_power_upper_970.trans
      change ((4385279698315297 / 281474976710656 : ℚ) : ℝ) ≤ ((4385279698315297 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (971 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height030.height_factor_upper_971.trans
      change ((12545151 / 281474976710656 : ℚ) : ℝ) ≤ ((12545151 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height030.height_power_upper_971.trans
      change ((2194888912409587 / 140737488355328 : ℚ) : ℝ) ≤ ((4389777824819174 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (972 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height030.height_factor_upper_972.trans
      change ((3058611 / 70368744177664 : ℚ) : ℝ) ≤ ((12234444 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height030.height_power_upper_972.trans
      change ((2197137957875851 / 140737488355328 : ℚ) : ℝ) ≤ ((4394275915751702 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (973 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height030.height_factor_upper_973.trans
      change ((11931469 / 281474976710656 : ℚ) : ℝ) ≤ ((11931469 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height030.height_power_upper_973.trans
      change ((4398773971138155 / 281474976710656 : ℚ) : ℝ) ≤ ((4398773971138155 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (974 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height030.height_factor_upper_974.trans
      change ((5818017 / 140737488355328 : ℚ) : ℝ) ≤ ((11636034 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height030.height_power_upper_974.trans
      change ((2201635995501893 / 140737488355328 : ℚ) : ℝ) ≤ ((4403271991003786 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (975 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height030.height_factor_upper_975.trans
      change ((709247 / 17592186044416 : ℚ) : ℝ) ≤ ((11347952 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height030.height_power_upper_975.trans
      change ((4407769975373817 / 281474976710656 : ℚ) : ℝ) ≤ ((4407769975373817 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (976 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height030.height_factor_upper_976.trans
      change ((11067039 / 281474976710656 : ℚ) : ℝ) ≤ ((11067039 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height030.height_power_upper_976.trans
      change ((1103066981068361 / 70368744177664 : ℚ) : ℝ) ≤ ((4412267924273444 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (977 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height030.height_factor_upper_977.trans
      change ((10793117 / 281474976710656 : ℚ) : ℝ) ≤ ((10793117 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height030.height_power_upper_977.trans
      change ((4416765837727839 / 281474976710656 : ℚ) : ℝ) ≤ ((4416765837727839 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (978 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height030.height_factor_upper_978.trans
      change ((2631503 / 70368744177664 : ℚ) : ℝ) ≤ ((10526012 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height030.height_power_upper_978.trans
      change ((2210631857881071 / 140737488355328 : ℚ) : ℝ) ≤ ((4421263715762142 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (979 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height030.height_factor_upper_979.trans
      change ((10265555 / 281474976710656 : ℚ) : ℝ) ≤ ((10265555 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height030.height_power_upper_979.trans
      change ((4425761558401471 / 281474976710656 : ℚ) : ℝ) ≤ ((4425761558401471 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (980 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height030.height_factor_upper_980.trans
      change ((2502895 / 70368744177664 : ℚ) : ℝ) ≤ ((10011580 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height030.height_power_upper_980.trans
      change ((1107564841417729 / 70368744177664 : ℚ) : ℝ) ≤ ((4430259365670916 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (981 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height030.height_factor_upper_981.trans
      change ((9763927 / 281474976710656 : ℚ) : ℝ) ≤ ((9763927 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height030.height_power_upper_981.trans
      change ((2217378568797769 / 140737488355328 : ℚ) : ℝ) ≤ ((4434757137595538 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (982 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height030.height_factor_upper_982.trans
      change ((9522437 / 281474976710656 : ℚ) : ℝ) ≤ ((9522437 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height030.height_power_upper_982.trans
      change ((2219627437100187 / 140737488355328 : ℚ) : ℝ) ≤ ((4439254874200374 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (983 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height030.height_factor_upper_983.trans
      change ((9286957 / 281474976710656 : ℚ) : ℝ) ≤ ((9286957 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height030.height_power_upper_983.trans
      change ((2221876287755217 / 140737488355328 : ℚ) : ℝ) ≤ ((4443752575510434 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (984 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height030.height_factor_upper_984.trans
      change ((4528669 / 140737488355328 : ℚ) : ℝ) ≤ ((9057338 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height030.height_power_upper_984.trans
      change ((4448250241550701 / 281474976710656 : ℚ) : ℝ) ≤ ((4448250241550701 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (985 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height030.height_factor_upper_985.trans
      change ((4416717 / 140737488355328 : ℚ) : ℝ) ≤ ((8833434 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height030.height_power_upper_985.trans
      change ((2226373936173065 / 140737488355328 : ℚ) : ℝ) ≤ ((4452747872346130 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (986 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height030.height_factor_upper_986.trans
      change ((8615103 / 281474976710656 : ℚ) : ℝ) ≤ ((8615103 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height030.height_power_upper_986.trans
      change ((4457245467921653 / 281474976710656 : ℚ) : ℝ) ≤ ((4457245467921653 : ℕ) : ℝ) / 2^48
      norm_num
  · have heq : i = (987 : Fin 988) := Fin.ext hi
    subst i
    constructor
    · apply Enclosures.Height030.height_factor_upper_987.trans
      change ((2105215725 / 140737488355328 : ℚ) : ℝ) ≤ ((4210431450 : ℕ) : ℝ) / 2^48
      norm_num
    · apply Enclosures.Height030.height_power_upper_987.trans
      change ((4461743028302173 / 281474976710656 : ℚ) : ℝ) ≤ ((4461743028302173 : ℕ) : ℝ) / 2^48
      norm_num
end LegendreK6.M2Pilot.FactorBounds.Height030
