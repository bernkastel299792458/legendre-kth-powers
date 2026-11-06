import LegendreK6.CHLRange
import LegendreK6.PrimeWitnesses

/-!
# The complete lower integer range

Primality of the 1259 small witnesses and the exponential joining inequalities
are checked by the Lean kernel. The only external mathematical parameter of this
module is `CHLRows`, the twelve explicitly stated corrected literature rows.
-/

namespace LegendreK6

theorem lower_range_complete (H : CHLRows) (n : ℕ) (hn : 1 ≤ n)
    (hupper : n ≤ 1242317999994) : NatSixthShort n := by
  by_cases hsmall : n ≤ 1259
  · exact small_range_prime n hn hsmall
  · exact chl_integer_coverage H n (by omega) hupper

theorem lower_log_range (H : CHLRows) (n : ℕ) (hn : 1 ≤ n)
    (hlog : Real.log ((n : ℝ) ^ 6) ≤ 167) : NatSixthShort n := by
  exact lower_range_complete H n hn (lower_join_of_log hn hlog)

end LegendreK6
