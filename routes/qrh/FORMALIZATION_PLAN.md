# End-to-end formalization work plan

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
