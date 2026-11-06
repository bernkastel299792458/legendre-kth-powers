# Milestone 2 working record

Started after milestone 1 checkpoint `b1d00a8` on 2026-11-06. This file is a
development log, not acceptance of milestone 2 or a full k=6 certificate.

The pilot cell is `[715/4,179]`, the worst cell in the frozen middle-range
certificate. Its rational starting log-height is `1841/64`, above `log(3e12)`;
the height kernel is still flat there. Thus the pilot does not require the
finite-height RH input. Lower cells may require that input later.

## Analytic implementation

- `IntegratedPsi` proves the actual finite von Mangoldt sum's four-point
  identity, nonnegative trapezoid weights, their `1/b` upper bound and strict
  interior support. It has no literature input.
- `TrapezoidKernel` proves the three bounds for actual complex powers by
  derivatives and the norm mean-value inequality. This avoids introducing a
  general bounded-variation or Mellin-transform formalization while retaining
  exactly the same kernel constants.
- `IntegratedExplicitFormula` states the classical original formula with
  actual zeta zeros, analytic multiplicities, and actual zeta derivatives in
  the affine terms. Its height-ordered limit is an external input. Four finite
  combinations and affine cancellation are proved; a weighted explicit
  formula is not substituted as an unproved input.
- `TrapezoidTrivial` proves summability of the actual trivial-zero primitives,
  exchanges their finite four-point combination, and proves its norm budget.
- `FiniteDensityGrid` proves an exact finite staircase bound by telescoping
  exponential differences, then the actual cumulative zero-weight bound from
  QRH, the unchanged CS rows and Rosser. Closed sigma endpoints are retained.
- `HeightGrid` proves the finite height upper sum with an explicit residual
  at the last node, including residual weights of lower zeros.

Each item above has been compiled individually. The replacement global proof
is not yet assembled and the entire enlarged project has not yet been rebuilt.

## Classical formula source check

In addition to the manuscript's Ingham reference, the original formula was
checked against A. J. Hildebrand, *Introduction to Analytic Number Theory*,
version 2013.01.07, Theorem 5.18, equation (5.32), printed page 166. Printed
page 167 expressly states absolute convergence of this zero sum. The definition
of the integrated Chebyshev function occurs on printed page 156. The PDF at
the [University of Athens course mirror][hildebrand] was downloaded locally;
pages 166 and 167 were rendered and visually checked. It is not redistributed.

The interface uses the weaker height-truncation limit of that absolutely
convergent formula, with actual multiplicities. It keeps the signs
`- (zeta'(0)/zeta(0))*t + zeta'(-1)/zeta(-1)`. This is a source-to-statement
check, not an independent proof of the classical formula in Lean.

## Numerical design and conservative variation

The original main double sum needs 1,517,568 cross exponential evaluations.
Factoring `exp(p*v)` at `p0=1/3`, `v0=2057/64`, and using the already formalized
Mathlib Taylor bound for `0 <= z <= 11` reduces this to 2524 factor exponentials
and finite rational moments. `LowRankTaylor` proves that algebraic bound;
`M2PilotDefinitions` proves the stable evaluation identities and weight signs.
The generator must prove every factor enclosure inside Lean. Arb proposes
witnesses only; its output is not an accepted correctness premise.

For this pilot, a conservative geometric height tail replaces the original
improper-integral expression. Heights grow by four, the cumulative envelope
grows by at most eight, and the quadratic residual decays by sixteen. The
proposed doubled residual bound is

`32*(4096/31)*q^2*exp(-2*U)*Phi(U)`.

It includes the residual of zeros below `exp(U)`. The generic finite geometric
prefix proof has compiled; the actual zero-envelope connection is in progress.
Exploratory Arb/rational arithmetic gives a new tail about `7.62405e-9` and
20-degree, 48-bit factor total about `0.93973603112`, still below `47/50`.
These are feasibility results, not completed Lean numerical certificates.
Original frozen scripts and numerical certificates remain unchanged.

The first concrete enclosure samples exposed an expression-translation issue:
the interval tactic needed explicit rational-to-real casts for the generated
rational constants. It was not a failure of the exponential estimate. After
that correction, the first and last sigma/height samples, including the final
geometric tail contribution, compiled successfully. Their axiom reports contain
only the standard three axioms, with no `Lean.ofReduceBool` or `sorryAx`.

## Analytic assembly checkpoint (numerical inequality still pending)

`M2PilotBudgetIdentity` now proves equality of the actual analytic budget and
`completeBudget`: the finite height sum and its doubled residual are exactly
the main exponential matrix plus the auxiliary baseline/second/third-column
terms. `M2PilotAnalytic.pilot_interval_of_complete_budget` is compiled. It
concludes the actual strict prime interval for every positive x with
`715/4 <= log x <= 179`, from QRH, CS v2, Rosser, the classical integrated
formula, and the one remaining numerical premise `completeBudget < 1`.
That premise is not yet discharged, so this is not the final pilot theorem.

The auxiliary budget has a compiled bound `<= 1/50000`, using exact finite
telescoping and kernel-checked exponential constants. Each of the actual
prime-power and trivial-zero budgets has a compiled bound `<= 1/1000000`.
The main sum has a compiled reduction to the positive low-rank moment bound.

All 2524 coefficient/power pairs have been proposed in 43 separate enclosure
modules. Their full kernel builds and the integer-moment certificate are in
progress. Python/Arb generation alone does not establish those bounds.
No completion percentage is inferred from module counts.

[hildebrand]: https://eclass-b.uoa.gr/modules/document/file.php/MATH717/04.%20%CE%92%CE%BF%CE%B7%CE%B8%CE%AE%CE%BC%CE%B1%CF%84%CE%B1/Analytic-number-theory-Hildebrand.pdf

## Milestone 2 completed proof checkpoint

The final `M2Pilot.pilot_short_interval_from_inputs` compiled successfully.
For every positive x with `715/4 <= log x <= 179`, it proves the actual
strict prime interval `ShortInterval6 x` from precisely QRH(7/8), CS v2,
Rosser's count and the classical integrated explicit formula. No numerical
budget, weighted zero estimate or local prime conclusion remains as an input.
All 43 enclosure blocks, 43 real-to-dyadic connection blocks, integer moments
and final aggregation passed. The complete budget is at most
`234943/250000 = 0.939772 < 47/50`. The final actual-dependency diagnostic
passed in 24.0 seconds, with only the standard three Lean axioms.

The human-readable note's height-index notation was corrected: moments use
the right endpoints `t_i = u_(i+1)`, not the starting node `u_0`. Lean already
used the correct indices. Original paper/certificates/reviews are preserved.
This checkpoint uses recorded incremental builds; it does not claim a new
clean whole-tree rebuild. The earlier aggregate report remains M1 evidence.
Full finite-range coverage, final assembly and final reproducible build
remain milestone 3 work; full conditional k=6 formalization is not complete.
