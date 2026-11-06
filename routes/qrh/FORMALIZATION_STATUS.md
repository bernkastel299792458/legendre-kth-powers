# Formalization status

**The end-to-end conditional k=6 Lean proof is not complete. The actual
infinite tail is now formalized relative to four named inputs.** The two
finite analytic ranges and their full transcendental certificates remain
open. See the [implementation plan](FORMALIZATION_PLAN.md) and
[dated evidence log](audit/formalization_progress_2026-11-06.md).

## Milestone 1: actual prime intervals in the infinite tail

`tail_short_interval_from_inputs` proves, for every real x > 0 with
log x >= 700, that an actual prime lies strictly in (x, x + 4*x^(3/4)).
Its mathematical inputs are `QRHSevenEighths`, `CSv2`, `RosserZeroCount`,
and `CHJIIShortInterval`, with their exact statements printed in the audit.

Actual zeta zeros, finite positive analytic multiplicities, conjugation,
real-axis nonvanishing, complex-power increments, the finite layer integral,
the CS table and Rosser reductions, actual psi/theta budgets, the common
CHJII truncation, and all six tail terms are connected. The final theorem
has no local prime conclusion, weighted-error bound, total-count corollary,
certificate soundness flag, or real-axis nonvanishing parameter.

See [TailFromInputs.lean](lean/LegendreK6/TailFromInputs.lean), the
[actual proof-dependency audit](audit/milestone1_dependencies.txt), and
[AI review with its precise scope](audit/milestone1_review.md). The aggregate
build evidence is recorded separately in `audit/lean_build_report.json`.

## Kernel-checked components

- Exact sixth-power algebra and strict endpoint reductions.
- The actual primality of all 1259 small-range witnesses, via 5349 recursive
  Lucas/Pratt nodes. This component does not assume Sorenson–Webster or trust
  the Python generator's primality decisions.
- The CHL integer ranges and exponential thresholds, with real exponentials
  proved by Mathlib's reflective interval tactic. Given the explicitly stated
  CHL literature rows, these establish the entire lower range through
  n = 1242317999994 and its overlap with L = 167.
- Exact rational checks and continuous real-parameter coverage of the 94 new
  and 60 inherited cells; saved rational maxima, margins, and 6% scaling.
- Four-point quadratic/affine identities; the exact exponential sigma-weight
  integral; common zero-weight domination and coefficient-scaling algebra.
- The six-term tail's numerical threshold, proved using kernel-checked exp/log
  bounds, and its analytic decay on the entire range L >= 700.
- Finite von Mangoldt weighted-sum extraction of an interior prime, given
  the explicitly stated weighted lower bound and support conditions.
- Actual prime-power budgets, strict theta endpoint extraction, and the
  complete infinite-tail theorem described above.
- The current assembly is `sixth_powers_of_finite_segment_inputs`, conditional
  on only the two finite analytic segment conclusions. The older three-field
  assembly remains as a general lemma, with its inputs explicitly visible.

The final build report identifies which of these source files were actually
compiled. `#print axioms` must be read together with `#check`: an extra local
conclusion supplied as a theorem argument does not appear as a custom axiom.

## Remaining end-to-end obligations

1. Precisely translate the integrated explicit formula and finite-height RH
   inputs for the smoothed ranges. The actual zero/multiplicity interface
   and QRH/CS inputs are now available; the accepted upstream results are
   not tasks to re-prove here.
2. The integrated explicit formula and its lawful pairing with the trapezoid
   and polynomial weights, including convergence, distributional endpoint
   atoms, and Mellin-transform bounds.
3. The smoothed Stieltjes upper sums, finite-height split, and analytic height
   tails. Milestone 1's finite real-part layer integral is reusable, but does
   not by itself establish these additional infinite-sum obligations.
4. Kernel-checkable transcendental enclosures for the complete 94-cell and
   60-cell sums. The existing Arb replays establish these computationally,
   but importing their saved rational outputs does not establish this bridge
   in Lean. The rational coverage theorems deliberately do not claim it.
5. Instantiate the proved actual prime-power budgets for both smoothed
   weights and prove their trivial-zero budgets, then remove the remaining
   `middle` and `far` inputs from the final theorem.

The unresolved obligations are not hidden behind renamed QRH/CS assumptions,
axioms, `sorry`, `native_decide`, or a blanket claim that a certificate is sound.
The paper contains the human-readable arguments; a future formalization must
produce the missing proof terms before this status can be upgraded.

## Reading the result correctly

The current strongest assembly has the complete input structure:

```text
QRHSevenEighths -> CSv2 -> RosserZeroCount -> CHJIIShortInterval ->
  CHLRows -> FiniteAnalyticSegmentInputs -> SixthPowerConclusion
```

`FiniteAnalyticSegmentInputs` contains only `middle` (167 <= log x <= 400)
and `far` (400 <= log x <= 700); the tail is supplied by its proved theorem.
This is still weaker than the final target with no local analytic conclusion
inputs. A standard-axioms-only audit does not discharge theorem parameters.

The agreed milestones concern the full project derivation relative to
individually enumerated literature inputs. Proving all those literature
theorems too, so that only QRH and CS remain as mathematical assumptions,
is a distinct, stronger scope and must not be conflated with this endpoint.

The PDF and historical reviews retain the original release's formalization
status. This document and subsequent dated build evidence record the new
implementation without expanding the historical reviewers' scope.
