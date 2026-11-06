import LegendreK6.LowerRange

/-!
# Conditional assembly: exact scope, not an end-to-end QRH+CS theorem

The three fields below are the local analytic segment conclusions from the
human-readable paper. They have NOT been derived here from QRH, CS, the explicit
formula, and certified transcendental arithmetic. They are explicit arguments,
not hidden axioms. Consequently, the last theorem is an assembly theorem only;
its successful compilation does not establish the full requested formal proof.

The lower range has a different status: given the explicitly cited CHL rows,
its integer witnesses, exponential thresholds, and interval coverage are proved
in the imported modules, with no local lower-range assumption remaining.
-/

namespace LegendreK6

/-- Remaining unformalized local analytic conclusions, deliberately exposed. -/
structure AnalyticSegmentInputs : Prop where
  middle : ∀ x : ℝ, 0 < x → 167 ≤ Real.log x → Real.log x ≤ 400 → ShortInterval6 x
  far : ∀ x : ℝ, 0 < x → 400 ≤ Real.log x → Real.log x ≤ 700 → ShortInterval4 x
  tail : ∀ x : ℝ, 0 < x → 700 ≤ Real.log x → ShortInterval4 x

theorem real_short_above_167_of_segment_inputs (H : AnalyticSegmentInputs)
    (x : ℝ) (hx : 0 < x) (hlog : 167 ≤ Real.log x) : ShortInterval6 x := by
  by_cases h400 : Real.log x ≤ 400
  · exact H.middle x hx hlog h400
  have hx1 : 1 ≤ x := by
    calc (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
      _ ≤ Real.exp (Real.log x) := Real.exp_le_exp.mpr (by linarith)
      _ = x := Real.exp_log hx
  apply short_six_of_short_four hx1
  by_cases h700 : Real.log x ≤ 700
  · exact H.far x hx (by linarith) h700
  · exact H.tail x hx (by linarith)

theorem nat_short_all_of_segment_inputs (HCHL : CHLRows) (H : AnalyticSegmentInputs)
    (n : ℕ) (hn : 1 ≤ n) : NatSixthShort n := by
  by_cases hlog : Real.log ((n : ℝ) ^ 6) ≤ 167
  · exact lower_log_range HCHL n hn hlog
  · apply nat_short_of_real_short n
    apply real_short_above_167_of_segment_inputs H ((n : ℝ) ^ 6)
    · exact pow_pos (by exact_mod_cast (show 0 < n by omega)) 6
    · linarith

/-- Conditional assembly only. This has extra local analytic input arguments. -/
theorem sixth_powers_of_segment_inputs (HCHL : CHLRows) (H : AnalyticSegmentInputs) :
    SixthPowerConclusion := by
  intro n hn
  exact conclusion_at_of_nat_short (nat_short_all_of_segment_inputs HCHL H n hn)

end LegendreK6
