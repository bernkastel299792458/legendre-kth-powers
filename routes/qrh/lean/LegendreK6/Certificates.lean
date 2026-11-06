import LegendreK6.CertificateData
import Mathlib.Tactic

/-! Kernel checks of the rational data already exported by the Arb program.
These theorems do not assert that any rational upper bound encloses the
transcendental zero-sum expression. That analytic/numerical bridge must be
proved separately; none is inserted here as an axiom. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace LegendreK6

def checkCells : List SavedCell → ℚ → ℚ → ℚ → Bool
  | [], start, finish, _ => decide (start = finish)
  | c :: cs, start, finish, target =>
      decide (c.left = start ∧ c.left < c.right ∧ 0 ≤ c.upper ∧ c.upper < target ∧
        0 ≤ c.scaledUpper ∧ c.scaledUpper < 1) &&
      checkCells cs c.right finish target

theorem refined_cell_count : refinedCells.length = 94 := by decide
theorem polynomial_cell_count : polynomialCells.length = 60 := by decide

/-- All 94 saved bounds, positive widths, and exact joins are kernel checked. -/
theorem refined_cells_checked : checkCells refinedCells 167 400 (47/50) = true := by
  norm_num [refinedCells, checkCells]

/-- The 60 inherited bounds and their conservative 6% scalings are kernel checked. -/
theorem polynomial_cells_checked : checkCells polynomialCells 400 700 1 = true := by
  norm_num [polynomialCells, checkCells]

theorem refined_saved_bounds_le_worst : ∀ c ∈ refinedCells,
    c.upper ≤ (234933999195957081190761 / 250000000000000000000000 : ℚ) := by
  norm_num [refinedCells]

theorem refined_saved_scaled_bounds_le_worst : ∀ c ∈ refinedCells,
    c.scaledUpper ≤ (124515019573857253031103 / 125000000000000000000000 : ℚ) := by
  norm_num [refinedCells]

theorem polynomial_saved_bounds_le_worst : ∀ c ∈ polynomialCells,
    c.upper ≤ (862339984538098379495241 / 10^24 : ℚ) := by
  norm_num [polynomialCells]

theorem refined_saved_margin :
    (1 : ℚ) - 234933999195957081190761 / 250000000000000000000000 =
      15066000804042918809239 / 250000000000000000000000 := by norm_num

theorem new_worst_bound_lt_target :
    (234933999195957081190761 / 250000000000000000000000 : ℚ) < 47/50 := by
  norm_num

theorem new_scaled_bound_lt_one :
    (124515019573857253031103 / 125000000000000000000000 : ℚ) < 1 := by
  norm_num

theorem inherited_scaled_bound_lt_one :
    (53/50 : ℚ) * (862339984538098379495241 / 10^24) < 1 := by norm_num

theorem tail_scaled_bound_lt_one : (53/50 : ℚ) * (14/25) = 371/625 ∧
    (371/625 : ℚ) < 1 := by norm_num

def checkIntegerChain : List (ℕ × ℕ) → ℕ → ℕ → Bool
  | [], previous, finish => decide (previous = finish)
  | row :: rows, previous, finish =>
      decide (row.1 ≤ previous + 1 ∧ row.1 ≤ row.2 ∧ previous ≤ row.2) &&
      checkIntegerChain rows row.2 finish

/-- This checks the integer endpoints only; the exp/log threshold obligations
are separate theorems in Thresholds.lean. -/
theorem chl_integer_chain_checked :
    checkIntegerChain chlIntegerRows 1259 1242317999994 = true := by decide

/-- Logical soundness of the finite cell checker: every listed cell has the
strict saved upper bounds it is supposed to have. -/
theorem checkCells_bounds {cells : List SavedCell} {a b target : ℚ}
    (h : checkCells cells a b target = true) :
    ∀ c ∈ cells, c.left < c.right ∧ 0 ≤ c.upper ∧ c.upper < target ∧
      0 ≤ c.scaledUpper ∧ c.scaledUpper < 1 := by
  induction cells generalizing a with
  | nil => simp
  | cons d ds ih =>
    simp only [checkCells, Bool.and_eq_true, decide_eq_true_eq] at h
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact ⟨h.1.2.1, h.1.2.2.1, h.1.2.2.2.1, h.1.2.2.2.2⟩
    · exact ih h.2 c hc

/-- Exact closed-interval coverage follows from the finite chain check. -/
theorem checkCells_cover {cells : List SavedCell} {a b target x : ℚ}
    (h : checkCells cells a b target = true) (hne : cells ≠ [])
    (ha : a ≤ x) (hb : x ≤ b) :
    ∃ c ∈ cells, c.left ≤ x ∧ x ≤ c.right := by
  induction cells generalizing a with
  | nil => exact (hne rfl).elim
  | cons d ds ih =>
    simp only [checkCells, Bool.and_eq_true, decide_eq_true_eq] at h
    by_cases hx : x ≤ d.right
    · exact ⟨d, List.mem_cons_self, by simpa [h.1.1] using ha, hx⟩
    · have hds : ds ≠ [] := by
        intro hz
        subst ds
        simp only [checkCells, decide_eq_true_eq] at h
        exact hx (h.2 ▸ hb)
      obtain ⟨c, hc, hcx, hxc⟩ := ih h.2 hds (le_of_lt (lt_of_not_ge hx))
      exact ⟨c, List.mem_cons_of_mem d hc, hcx, hxc⟩

theorem refined_rational_coverage {x : ℚ} (ha : 167 ≤ x) (hb : x ≤ 400) :
    ∃ c ∈ refinedCells, c.left ≤ x ∧ x ≤ c.right :=
  checkCells_cover refined_cells_checked (by decide) ha hb

theorem polynomial_rational_coverage {x : ℚ} (ha : 400 ≤ x) (hb : x ≤ 700) :
    ∃ c ∈ polynomialCells, c.left ≤ x ∧ x ≤ c.right :=
  checkCells_cover polynomial_cells_checked (by decide) ha hb

/-- The endpoints are rational, but their closed cells also cover every real
parameter in the stated range, not merely the rational sample points. -/
theorem checkCells_cover_real {cells : List SavedCell} {a b target : ℚ} {x : ℝ}
    (h : checkCells cells a b target = true) (hne : cells ≠ [])
    (ha : (a : ℝ) ≤ x) (hb : x ≤ (b : ℝ)) :
    ∃ c ∈ cells, (c.left : ℝ) ≤ x ∧ x ≤ (c.right : ℝ) := by
  induction cells generalizing a with
  | nil => exact (hne rfl).elim
  | cons d ds ih =>
    simp only [checkCells, Bool.and_eq_true, decide_eq_true_eq] at h
    by_cases hx : x ≤ (d.right : ℝ)
    · exact ⟨d, List.mem_cons_self, by simpa [h.1.1] using ha, hx⟩
    · have hds : ds ≠ [] := by
        intro hz
        subst ds
        simp only [checkCells, decide_eq_true_eq] at h
        exact hx (by simpa only [h.2] using hb)
      obtain ⟨c, hc, hcx, hxc⟩ := ih h.2 hds (le_of_lt (lt_of_not_ge hx))
      exact ⟨c, List.mem_cons_of_mem d hc, hcx, hxc⟩

theorem refined_real_coverage {x : ℝ} (ha : 167 ≤ x) (hb : x ≤ 400) :
    ∃ c ∈ refinedCells, (c.left : ℝ) ≤ x ∧ x ≤ (c.right : ℝ) :=
  checkCells_cover_real refined_cells_checked (by decide) (by norm_num; exact ha)
    (by norm_num; exact hb)

theorem polynomial_real_coverage {x : ℝ} (ha : 400 ≤ x) (hb : x ≤ 700) :
    ∃ c ∈ polynomialCells, (c.left : ℝ) ≤ x ∧ x ≤ (c.right : ℝ) :=
  checkCells_cover_real polynomial_cells_checked (by decide) (by norm_num; exact ha)
    (by norm_num; exact hb)

end LegendreK6
