# Formalization status

**Complete and accepted: the downstream k=6 Lean proof from seven individually
named external inputs. All 241 modules passed an isolated whole-tree rebuild
and its matching exact-input dependency audit.** All local analytic-segment
and numerical-budget premises have been discharged.

## Exact theorem and scope

The final theorem is `LegendreK6.sixth_powers_from_named_inputs` in
[FinalResult.lean](lean/LegendreK6/FinalResult.lean):

```text
QRHSevenEighths -> CSv2 -> RosserZeroCount -> IntegratedExplicitFormula ->
  FiniteRH3e12 -> CHJIIShortInterval -> CHLRows -> SixthPowerConclusion
```

For every integer n >= 1, it concludes that an actual `Nat.Prime` lies
strictly between n^6 and (n+1)^6. The companion theorem
`sixth_power_short_from_named_inputs` proves `n^6 < p < n^6 + 6*n^5`.
No analytic-segment conclusion, weighted zero estimate, numerical correctness
flag or local prime conclusion is a final theorem parameter. Older generic
assembly lemmas retain their original, explicitly displayed parameters.

The seven external inputs have precise versions and domains: see the
[readable addendum](paper/lean_formalization_addendum.md) and the definitions
in `DensityInput`, `LiteratureInputs`, `IntegratedExplicitFormula`,
`FiniteRHInput`, and `CHLRange`. QRH and CS v2 alone are **not** the full input
list. Re-proving the other cited theorems in Lean is a distinct, stronger
task. The metadata flag `end_to_end_H1_H2_formalization` therefore remains
false; it is not the flag for the agreed downstream proof with named inputs.

## Completed mathematical connections

| Part | Range | Actual proof |
|---|---|---|
| Integer lower range | 1 <= n <= 1242317999994, overlapping log x = 167 | 1259 prime witnesses, 5349 Lucas/Pratt nodes, corrected CHL rows, proved exponential joins |
| Lower middle | 167 <= log x <= 178.75 | Finite RH below 3e12, actual kernel comparison, rational sigma multipliers and integer moments |
| Upper middle | 178.75 <= log x <= 400 | Complete difficult pilot and proved continuous density/height translation |
| Far range | 400 <= log x <= 700 | New fourth-power-length trapezoid pilot and continuous translation |
| Infinite tail | log x >= 700 | Actual zero sums, density integration, arithmetic subtraction and CHJII's shared truncation |

The proof uses the actual zeta function, analytic zero multiplicities,
conjugation, internally proved real-axis nonvanishing, actual complex powers,
integrated Chebyshev sums, weighted von Mangoldt sums, prime-power subtraction
and strict endpoint extraction.

`FinalCellCoverage.lean` gives actual prime conclusions on each of the 94
historical middle cells and 60 historical far cells. Saved rational maxima
are not accepted as evidence of their transcendental expressions.

The far formal proof uses the already formalized trapezoid weight. This is
a disclosed method change, not a line-by-line translation of the historical
polynomial-weight argument. The original manuscript, certificate programs,
numerical certificates and reviews are preserved; the addendum describes
the proof actually used in Lean.

## Kernel numerical bounds

The difficult pilot's complete budget is at most `0.939772`. The lower-middle
comparison uses rational sigma factors 64, 3/2 and 1, with complete budget
at most `0.966283`. The new far pilot's budget is at most `0.450022`.
All are strictly below one.

Every required real factor enclosure is checked in Lean. Positive Taylor
expansion reduces the exponential matrix to integer moments. The rational
inequalities use ordinary `decide +kernel`. Python and Arb propose data;
their correctness is not a theorem premise. No local `sorry`, custom
mathematical axiom, `native_decide` or `Lean.ofReduceBool` shortcut is used.

The old 6% coefficient-sensitivity certificate concerns the original written
argument. It is not automatically a theorem about the new, more conservative
formal lower-middle budget.

## Final acceptance evidence

The incremental final dependency diagnostic passed in 27.562 seconds. It
prints the complete seven-input types and checks that the actual tail,
lower, middle, far, primality, analytic and numerical proofs occur in the
final transitive proof dependency closure:
[incremental record](audit/final_dependencies_incremental.txt).
The reported axioms are `propext`, `Classical.choice`, and `Quot.sound`.

Final acceptance passed on 2026-11-06. All **241/241** modules rebuilt into a
previously nonexistent output directory in **2690.618 seconds**, with
pinned sources, dependencies and `autoImplicit=false`. All source and artifact
hashes were checked before and after compilation. The matching dependency
diagnostic passed in **17.375 seconds** against those fresh artifacts.

- [Complete build report](audit/builds/final-20261106/lean_build_report.json)
- [Matching dependency report](audit/builds/final-20261106/final_dependency_report.json)
- [Full types, actual dependency closure and axioms](audit/builds/final-20261106/final_dependencies.txt)
- [Acceptance checkpoint](audit/milestone3_checkpoint.json) and [audit index](audit/README.md)

The final theorem and both cell-coverage theorems have only `propext`,
`Classical.choice`, and `Quot.sound` in their axiom reports. The seven
mathematical hypotheses remain explicit theorem parameters, rather than
custom kernel axioms. The isolated local build is the acceptance evidence;
GitHub CI results must be reported separately for their actual revision.

Historical records remain separate: M1 commit `b1d00a8` and its 58-module
build; M2 commit `a136d67` and its incrementally checked pilot. They are not
relabeled as builds of later sources. Review reports identify implementation
overlap and do not claim human peer review.

See [reproduction commands](REPRODUCING.md), [the plan](FORMALIZATION_PLAN.md),
[the M3 log](audit/milestone3_worklog.md), and [AI disclosure](AI_USE.md).
