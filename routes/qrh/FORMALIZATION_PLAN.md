# End-to-end formalization work plan

**Current status: all three milestones accepted; see the final checkpoint at the end.**
The earlier plan and progress statements below are retained chronologically.

Started: 2026-11-06, following the project owner's explicit instruction to
execute the three milestones. This is an implementation plan and progress
record, not an assertion that the final theorem has been obtained.

## Completion contract

The agreed first endpoint is the complete derivation of the k=6 conclusion
from QRH(7/8), CS v2, and individually named, accurately translated classical
literature inputs. No conclusion newly derived in this paper may remain as
an unexplained theorem parameter. In particular, the three fields of
`AnalyticSegmentInputs` must disappear from the final theorem's input list.

A stronger endpoint, with QRH and CS as the *only* mathematical assumptions
and all other cited literature proved in Lean too, is distinct. Every report
must display the complete mathematical input list and must not confuse these
two scopes. Neither the accepted upstream proofs nor a green build of
unconnected components proves this project's downstream argument.

## Milestone 1: close the infinite tail

- Actual von Mangoldt and Chebyshev prime-power budgets and strict endpoints.
- Actual zeta zeros, analytic multiplicities, compact truncations, conjugation,
  and correct treatment of the real axis.
- Exact QRH, CS v2, Rosser, and CHJII inputs, with source/statement review.
- Actual complex-power increments and the finite real-part layer integral.
- Derivation of the three zero-density terms, all parameter domains, and
  the other three tail terms.
- Produce `ShortInterval4 x` for every positive x with `log x >= 700`, using
  only the named external inputs; remove the local tail conclusion input
  from the new assembly theorem.

## Milestone 2: one complete difficult middle cell

- Precise integrated explicit formula input and convergence convention.
- Actual trapezoid weighted sum, all four corner contributions, Mellin bounds,
  real-part integration, finite-height split, and height-tail bounds.
- Kernel-checkable enclosures of the complete transcendental expression for
  a difficult cell. Importing a saved rational maximum alone does not qualify.
- A theorem concluding an actual interior `Nat.Prime`, with no assumed
  weighted budget, cell correctness flag, or local prime conclusion.

## Milestone 3: all cells and final assembly

- Extend to all 94 trapezoid cells and the 60 polynomial cells.
- Prove the polynomial weight's complete analytic bounds and endpoints.
- Assemble lower range, both finite analytic ranges, and the infinite tail.
- Audit complete theorem types, transitive proof dependencies, and axioms.
- Reproduce from the pinned sources and document the exact input list.

## Evidence rules

Only successfully compiled proof terms count as formal progress. Report
which remaining mathematical premise has actually been discharged; do not
report a completion percentage based on file count. Failed approaches and
unproved obligations remain in the log. The numerical certificate and paper
snapshots are retained; new proof work is separately versioned.

Implementation evidence is recorded in [the progress log](audit/formalization_progress_2026-11-06.md).

## Accepted progress, 2026-11-06

Milestone 1 is complete relative to its four named inputs (commit `b1d00a8`).
Milestone 2 now has a compiled final strict-prime theorem on
`715/4 <= log x <= 179`, with no numerical budget parameter; its complete
input list and actual dependencies are recorded in
`audit/milestone2_dependencies.txt`. The 86 numerical blocks and final
aggregation passed. These are incremental build records, not a new clean
whole-tree rebuild. Milestone 3 and the final reproducible build remain open.

## Milestone 3 method refinement

M2 is preserved in commit `a136d67`. The final target and both finite-range
coverage obligations remain unchanged. A new proved density-grid translation
allows one verified budget to cover continuously translated log-x intervals.
Exploratory Arb checks show the already formalized trapezoid also suffices for
the fourth-power far range, with a new pilot at `[400,400.25]`. We therefore
pursue that weight for the formal far proof, rather than a separate derivation
of the original polynomial weight. This is a disclosed change of proof method:
covering the original 60 far cells by this new theorem will not mean that the
old polynomial-weight derivation was translated line by line into Lean.
The old manuscript and certificates remain preserved; a new readable proof
note and final input list must describe the method actually used.

For the lower middle range, finite RH through 3e12 controls low zeros.
A comparison with the M2 reference kernel and three rational sigma factors
(64, 3/2, 1) appears to cover `[167,715/4]` with the existing height certificate.
The exact comparison and the changed integer moments still require proof.
No feasibility number in this paragraph is accepted as a Lean premise.

## Milestone 3 and final acceptance, 2026-11-06

All three milestones are complete relative to the seven named external
inputs. The isolated build compiled all 241 current modules successfully
in 2690.618 seconds. The matching final dependency audit passed in 17.375
seconds, with all required actual proof dependencies and only the standard
three axioms. No local analytic-segment conclusion or numerical-budget
premise remains in the final theorem.

The final result covers every positive integer, and every point of the
94 middle and 60 far cells. The far obligation is discharged using the
disclosed trapezoid method refinement; the old polynomial-weight derivation
was not translated line by line. The lower-middle budget is 0.966283,
the difficult pilot budget 0.939772, and the far pilot budget 0.450022.
All required real enclosures and integer inequalities are kernel-checked.

Exact external inputs: QRHSevenEighths, CSv2, RosserZeroCount,
IntegratedExplicitFormula, FiniteRH3e12, CHJIIShortInterval, CHLRows.
The stronger QRH/CS-only formalization is not claimed. Four original
numerical certificates also replayed successfully in 232.797 seconds,
with protected source/data/summary hashes unchanged; six generated-source
checks passed. The original manuscript and historical reviews are preserved.

Acceptance records are under `audit/builds/final-20261106/` (or
`builds/final-20261106/` relative to the audit directory). See
`audit/milestone3_checkpoint.json`, the audit index, and
`FORMALIZATION_STATUS.md` for final scope and provenance. Earlier entries
in this log describe their historical checkpoint, not remaining local gaps.
