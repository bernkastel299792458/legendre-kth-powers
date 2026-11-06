# Milestone 2 analytic-chain cross-review

Date: 2026-11-06. Reviewer: Codex sub-agent `lean_prime_power_budget`.

**Final disposition: PASS for milestone 2, relative to the four explicitly
named QRH, CS v2, Rosser, and integrated-explicit-formula inputs. The completed
pilot theorem covers `715/4 <= log(x) <= 179`, with an actual strict prime
conclusion and no remaining numerical-budget premise. This is not completion
of the full k=6 formalization.**

Sections 1–12 preserve the successive review checkpoints. Their earlier
PENDING statements are superseded by the final evidence and judgment in
Section 13; they are retained to distinguish what was known at each stage.

## Scope, independence, and evidence

The reviewer read `FiniteDensityGrid`, `HeightKernel`, `HeightGrid`,
`GeometricHeightTail`, `DensityGridGrowth`, `TrapezoidKernel`,
`TrapezoidTrivial`, `TrapezoidZeroBound`, and `TrapezoidHeightBound`.
The reviewer did not implement these modules. Their assessment is an additional
AI cross-check by an agent distinct from their implementers, not human peer
review. The inherited actual-zero and literature interfaces were checked
against the milestone 1 audit; the CS derivation itself was not re-audited.

The reviewer implemented `IntegratedPsi`, `IntegratedExplicitFormula`,
`MiddleDomains`, `TrapezoidPrime`, and `M2PilotGrid`, as well as the earlier
prime-power budget. Discussion of those modules below is self-review. The whole
chain must not be described as wholly independently reviewed by this agent.

This combines source-level mathematical/parameter review with inspection of
the recorded final numerical and proof-dependency audits. The reviewer compiled
their own modules and relevant signature/axiom probes, but did not personally
rerun the final assembled diagnostic or aggregate build. Those final records
were produced by the other agents and inspected as detailed in Section 13.
The source hashes below and the numerical build manifest identify the reviewed
snapshot. The completed evidence is an incremental build, not a clean rebuild
of the enlarged repository.

## 1. Actual zeros, multiplicities, and closed endpoints

`allZetaZeros T` is the finite set of actual zeros of Mathlib's `riemannZeta`
with `0 < Re(rho) < 1` and `|Im(rho)| <= T`. The construction initially includes
any possible real-axis zero. `zetaMultiplicity` is `analyticOrderNatAt`, not a
constant multiplicity of one. Its finiteness and positivity at zeros, and its
invariance under conjugation, have been proved. Real-axis nonvanishing in the
open strip is proved in `ZetaZeros`; it is not an extra input to the M2 bounds.

Positive-height counts include `0 < gamma <= T`. Density counts use
`sigma <= beta`, and the CS row domains include both endpoints. Thus a zero
on a height cutoff, on a sigma node, or at `beta = 7/8` is retained.
Restricting the source's strip count to the project's open-strip count weakens
an upper bound; it does not posit a stronger density theorem. The pairing
identity used by `TrapezoidZeroBound` preserves the true multiplicities and
supplies exactly one factor of two for the two signs of gamma.

## 2. Classical integrated formula: source translation

The reviewer visually checked the rendered original of Hildebrand,
*Introduction to Analytic Number Theory*, version 2013.01.07, printed pages
166 and 167. Theorem 5.18, equation (5.32), states the integrated formula for
`x >= 1`. In the project's notation its right side is

```text
x^2/2 - sum_rho x^(rho+1)/(rho*(rho+1))
      - (zeta'(0)/zeta(0))*x + zeta'(-1)/zeta(-1)
      - sum_{n>=1} x^(1-2*n)/(2*n*(2*n-1)).
```

In particular the constant affine term has a plus sign. The Lean input has
these signs, uses the actual zeta derivatives, and uses only `x > 1`, a
restriction of the source domain. Printed page 167 explicitly says the
nontrivial-zero series for the integrated formula converges absolutely; its
(5.34) gives the convergent inverse-square zero sum. This supports taking
closed symmetric height truncations without an exceptional sequence of heights.

The source says that rho runs through all nontrivial zeros. The inspected pages
do not separately spell out the words “counted with multiplicity.” The Lean
interface makes the usual analytic zero-sum convention explicit by weighting
each distinct zero by its analytic order. This report does not misquote those
words as appearing on the inspected pages. A future bibliography clarification
could add a source which states that convention verbatim; no simplicity
assumption is used in the formal development.

`IntegratedExplicitFormula` is an explicitly named external classical input,
not a theorem proved by this repository. It asserts the height-limit consequence
of the displayed formula for actual `integratedPsi` and actual zeros. It does
not assume a trapezoid formula, a weighted-zero bound, or a prime conclusion.
The four-point application, affine cancellation, quadratic main term `h`, and
passage through the four limits are proved downstream. The input remains
visible in the prime-extraction theorem even though it is unnecessary for the
separate upper bound on finite zero sums.

Source: [Hildebrand lecture notes][hildebrand]. The PDF was independently read
for this review; the classical formula itself was not re-proved.

## 3. Trapezoid operator and strict prime extraction

`IntegratedPsi` uses the actual finite von Mangoldt sum
`sum_{1 <= m <= floor(t)} Lambda(m)*(t-m)`. At an integer endpoint the extra
term is zero. Cutoff extension to any larger finite bound is proved using
positive parts, so the four-point finite-sum identity uses actual arithmetic
objects rather than a surrogate function.

For positive `a <= b`, `a+b=1`, and `h>0`, the actual weight is nonnegative,
is at most `1/b`, and vanishes at and outside both endpoints. Positive weight
therefore implies the strict interval `x < m < x+h`. The prime-power estimate
is applied to the actual nonprime von Mangoldt contribution. `TrapezoidPrime`
is a valid general interface: it still has explicit uniform-zero, actual
trivial-term, and scalar budget hypotheses. Those hypotheses must be supplied
before it becomes a pilot-cell theorem. They are not silently treated as proved.

## 4. Kernel constants and the trivial-zero series

For an actual nontrivial zero the kernel proofs give the three envelopes

```text
h*x^(beta-1),
h*x^(beta-1)*(2/b)*q/|gamma|,
h*x^(beta-1)*(4/(a*b))*q^2/|gamma|^2,
```

where `q=(x+h)/h`. With `a=1/32`, `b=31/32`, the two coefficients are `64/31`
and `4096/31`. The first bound uses the two finite differences, the second
uses the two increments of length `a*h`, and the last bounds all four
primitive terms. The minimum is therefore an upper bound with the stated
constants. Nonzero denominators and nonzero gamma are proved for the actual
zeros; no zero simplicity or omitted real zero is assumed.

The trivial-zero proof does not use the gamma-decay bound at gamma zero.
It uses the base estimate at `rho=-2*(j+1)`. Primitive terms and kernel terms
have proved geometric absolute majorants for `x>1`; the four pointwise
summable series can therefore be combined. This proves the actual identity
between `trapezoidTrivialDifference` and the kernel series, followed by

```text
norm(trapezoidTrivialDifference x h a b)
  <= h*x^(-3)/(1-x^(-2)).
```

There is no unproved interchange of an arbitrary `tsum` in this step.

## 5. Sigma grid and growth of the density envelope

The sigma staircase is a finite inequality retaining the condition
`s(j) <= beta`. Its exponential increments are nonnegative for `A>=0`
and monotone sigma nodes. Multiplication by actual nonnegative analytic
multiplicities and finite summation produces the weighted count estimate.
The base term is controlled by the derived Rosser bound, and every increment
is controlled by a CS v2 row. The result is an upper bound on the actual
`positiveZeroWeight`, not an assumed bound on an abstract zero model.

The logarithmic-height CS expression is derived with
`p=3*(1-sigma)/(2-sigma)` and logarithmic exponent `p+2`. On the needed sigma
range, `0<=p<=1` and `2<=p+2<=3`. For `U>=6` and `v>=0`, the estimate

```text
exp(p*(U+v))*(U+v)^r <= exp(3*v/2)*exp(p*U)*U^r
```

uses `r<=3` and `log(1+v/U)<=v/U`. It also applies to the base term and the
lower-degree CS terms. All CS coefficients and sigma increments used to sum
these bounds have proved nonnegativity. Taking `v=k*log(4)` yields
`Phi(U+k*log(4)) <= 8^k*Phi(U)`; monotonicity or a separate unproved growth
bound for Phi is not an input.

## 6. Height grid, retained low-height residual, and factors 16/32

The finite height decomposition retains the residual
`g(max(gamma,R))`, where `R` is the last height. It does not replace that
residual by a sum over `gamma>R`. Consequently every zero below the last
height retains its residual contribution. The initial flat-kernel condition
`g(firstHeight)=1` controls zeros below the first node.

Grid masses are `g(height_j)-g(height_(j+1))`. Their nonnegativity is proved
from kernel antitonicity and increasing heights before multiplication by a
count upper bound. The prefix cutoff is closed. A prefix of any finite
truncation is bounded by the actual count at the prefix height; there is no
assumption that the original truncation lies below that height.

The geometric residual proof bounds the whole finite weighted sum of
`C/max(gamma,R)^2`. Heights grow by four, the density envelope by eight, and
the quadratic envelope decays by sixteen. The prefix at index `k+1` gives
`8^(k+1)`, so the coefficient is

```text
8 * sum_{k>=0}(8/16)^k <= 8*2 = 16.
```

A finite cover of every original cutoff is proved; an unproved infinite
summation over actual zeros is unnecessary. The resulting positive-height
residual is `16*C/R^2*Phi(log R)`. The full zero norm estimate subsequently
multiplies the entire positive-height budget by two. Thus the corresponding
full residual coefficient is **32**, exactly as used by the pilot height
coefficient. No missing low-height residual, sign reversal, or missing/doubled
conjugation factor was found in this chain.

## 7. Final analytic theorem: actual objects and visible parameters

`norm_truncatedTrapezoidZeroSum_le_heightBudget` concludes

```text
norm(truncatedTrapezoidZeroSum (exp L) h (1/32) (31/32) T)
  <= h * (2 * trapezoidHeightBudget s row nSigma A q u nHeight).
```

Its analytic inputs are exactly `QRHSevenEighths`, `CSv2`, and
`RosserZeroCount`. Its other premises are explicit grid and parameter facts:
`h>0`, `0<=A<=L`, `q>=0`, `(exp L+h)/h<=q`, monotone sigma nodes beginning
at `1/2` and ending at least `7/8`, valid CS rows, monotone height nodes,
first height at least `3*10^12`, first log height at least one, final log
height at least six, and the initial kernel value one. No `hZ` zero-budget
premise, hidden real-axis nonvanishing input, prime-existence premise, or
project-specific density estimate is required by this theorem.

The statement is uniform in the actual finite cutoff `T`. Together with the
separately named integrated-formula input it can supply the analytic limit
step used for strict prime extraction. It does not itself prove that the
resulting scalar budget is below one.

## 8. Pilot conversion reviewed so far and pending obligations

`M2PilotGrid` proves the finite sigma and height grids, closed CS row domains,
monotonicity and endpoint identities. Its actual interval is
`715/4 <= L <= 179`. The sigma and height powers lie in `[0,2/3]` and
`[0,33/2]`, respectively, giving a product at most 11. The two narrowly needed
logarithm comparisons are obtained from separately proved rational exponential
enclosures in `M2PilotConstants`. This portion is self-review by its implementer.

At the recorded snapshot, `M2PilotExpression` establishes the exact sigma
weight conversion, the CS expression at a log height, and a low-rank upper
bound for the defined main budget. The expression uses the correct exponent
`p+2`, and the finite range-to-`Fin` changes of indices preserve every term.
The complete connection was still under implementation at the initial
snapshot. It has since been supplied and source-reviewed in the addendum below;
that addendum supersedes this initial pending item.

Before an M2 completion judgment, the following remain to be reviewed together:

- Every required sample/factor enclosure and the complete scalar estimate
  `Z+P+V<1`, proved with the intended outward error bounds.
- The actual strict `Nat.Prime` pilot conclusion with no unproved local-budget
  parameter, and its full theorem type and proof-dependency audit.
- An aggregate build of the finalized modules, followed by a review bound to
  those exact source hashes.

The module count, absence of `sorry`, and successful compilation of isolated
lemmas cannot discharge these obligations. No full k=6 conclusion follows
from this report.

## 9. Addendum: complete budget identity and conditional pilot theorem

After the initial review, the reviewer read `M2PilotBudgetIdentity` and
`M2PilotAnalytic`, together with the definitions in `M2PilotBudgetDefinitions`
and the intervening `TrapezoidCell`/`TrapezoidGridCell` assembly. These modules
were implemented by the root agent, not this reviewer. Their individual native
compilations were reported successful by the implementer; the reviewer did
not rerun those compilations or an aggregate build.

The identity is exact, not a numerical approximation. Writing `u_i` for
`height i`, the reviewed coefficient is

```text
H_i = 2*u_i^2*mass_i
      + (if i=987 then 32*(4096/31)*z(u_i)^2*u_i^2 else 0).
```

The intermediate sum is `sum_i H_i*Phi(u_i)/u_i^2`. Every `u_i` is proved
positive, so cancellation is legitimate. Its ordinary part becomes
`2*sum_i mass_i*Phi(u_i)`. The final-node term is selected exactly once and
becomes `32*(4096/31)*z(U)^2*Phi(U)`. Since
`z(U)^2=q^2*exp(-2*U)` and `node 988=height 987=U`, this is precisely twice
the full positive-height residual. It is neither omitted nor counted again
in the ordinary mass sum.

The second exact identity divides the complete CS expression by `u_i^2`:

```text
Phi(u_i)/u_i^2
  = sum_j sigmaCoefficient_j*exp(p_j*(u_i+log(u_i)))
    + D + E/u_i + exp(-left/2+u_i)/u_i.
```

Thus the `B2` aggregate `D`, the `B3` aggregate `E/u_i`, and the Rosser base
term all remain in `auxiliaryBudget`, with the same full height coefficient
including its tail part. The main term is merely a finite double sum with its
order exchanged. No factor of two or `u_i^2` is lost in these operations.
`analytic_budget_eq_completeBudget` therefore connects the actual analytic
budget, actual prime-power budget, and actual trivial-zero budget exactly:

```text
2*trapezoidHeightBudget s rowNat 1536 left q node 988
  + middlePrimePowerBudget left right + cellTrivialBudget left
  = completeBudget.
```

The final conditional interface `pilot_interval_of_complete_budget` has these
premises and no additional zero-budget or grid premises:

```text
QRHSevenEighths
CSv2
RosserZeroCount
IntegratedExplicitFormula
completeBudget < 1
x > 0
715/4 <= log x <= 179.
```

Its conclusion is `ShortInterval6 x`, which unfolds to an actual natural
prime strictly between `x` and `x+6*x^(5/6)`. The finite-grid hypotheses are
supplied by proved pilot facts. The uniform truncated-zero bound is derived
from the first three inputs, and the classical integrated formula is used
for the limiting weighted identity. The actual trivial budget is supplied
by its monotonicity on the cell. There is no assumed local prime conclusion.

**Addendum disposition:** the completed analytic-to-numerical interface passes
this source-level cross-review. `completeBudget < 1` remains an explicit
undischarged premise at this review stage. The factor/sample certificates,
complete numerical inequality, final dependency audit and finalized build
remain pending; M2 is not declared complete.

## 10. Recorded analytic dependency and kernel audit

The reviewer has now read both `Milestone2AnalyticDependencies.lean` and its
recorded output `milestone2_analytic_dependencies.txt`. The diagnostic traverses
project constants appearing in the final analytic theorem's type and proof
terms, recursively, and fails if any required analytic dependency is absent.
The recorded run reaches
`MILESTONE2_ANALYTIC_DEPENDENCIES_PRESENT_NUMERICAL_PREMISE_REMAINS`.

The printed theorem type has exactly the four literature inputs, the numerical
premise `completeBudget < 1`, and the stated positive-x/log-cell conditions.
The axiom report is `[propext, Classical.choice, Quot.sound]`; it contains no
`sorryAx`, custom mathematical axiom, or `Lean.ofReduceBool`. The actual proof
closure includes the integrated finite-sum identity and height limit, kernel
bounds, real-axis nonvanishing, multiplicity-preserving conjugation, actual
sigma-density estimates, full geometric residual, actual prime-power bound,
strict prime extraction, and the exact complete-budget identity.

These records support the analytic assembly already source-reviewed. They do
not certify the missing numerical inequality. The root agent also reports a
successful recompilation of `M2PilotAnalytic` with `-DautoImplicit=false`.
This reviewer inspected the diagnostic and its output, but did not execute a
new dependency run or aggregate rebuild.

## 11. Integer certificate and 48-bit moment semantics

The reviewer read `LowRankTaylor`, `LowRankInteger`, `M2PilotIntegerData`, and
`M2PilotIntegerCertificate`. None was implemented by this reviewer. No indexing,
scaling, or Taylor-remainder defect was found in this additional source review.
The reviewer did not recalculate the integer certificate or rerun its build.

`integerMoment rows n` sums `c*a^n` over the list of natural-number pairs.
`integerMoment_eq_sum` identifies `List.map` with `List.ofFn` and uses
`List.sum_ofFn` to prove equality with the sum over **all indices**
`Fin rows.length`. It does not turn the rows into a set or discard duplicate
rows. This is a proved list-to-indexed-sum equality, not an assumed reindexing.

For the pilot, the two list lengths reduce to 1536 and 988 (`rfl` proves
the displayed length equalities). `sigmaRowIndex` and `heightRowIndex` retain
the original index value exactly. Because these lengths are definitionally
the displayed finite bounds, the specialized functions identify with the
corresponding generic dyadic functions; proof irrelevance handles the bound
proofs in `Fin`. There is no offset, permutation, or truncation in the
specialization used by `dyadicLowRank20_le`.

Both entries of a row are scaled by `2^48`: the coefficient is `c/2^48`,
and the power variable is `a/2^48`. Consequently the exact n-th moment is

```text
sum_i (c_i/2^48)*(a_i/2^48)^n
  = (sum_i c_i*a_i^n)/2^(48*(n+1)).
```

This equality is proved termwise in `dyadicMoment_eq_rationalMoment` for
arbitrary bit width and arbitrary n. Products of the sigma and height moments
therefore carry the two factors of this denominator, equivalently
`2^(96*(n+1))` at 48 bits. No integer truncating division is used: the
moments are natural-number sums cast to exact rational numbers before division.
Their cast to real numbers is also proved to equal the real finite moments.

The rational majorant sums degrees 0 through 20, dividing the product of the
two degree-n moments by `n!`, and adds twice their degree-21 product divided
by `21!`. These are precisely the terms of `lowRankTaylor20`. The analytic
Taylor estimate uses `0 <= z <= 11` and Mathlib's remainder condition
`z/(21+1) <= 1/2`. The remainder factor two is retained. Monotonicity of the
majorant is proved for nonnegative coefficients and powers, including the
remainder; it justifies replacing them by pointwise upper enclosures.
The upper dyadic powers do not themselves need a new product-at-most-11
premise at this monotonicity step: that domain condition was applied to the
original analytic powers before the polynomial was enlarged.

`rationalLowRank20_le` has no hypotheses and asserts the exact rational
bound `<= 3759/4000`. Its implementation is `decide +kernel`, rather than
`native_decide`; the implementer reports successful kernel evaluation.
`dyadicLowRank20_le` transfers that result to the displayed real moment sum
using the proved equality and order-preserving rational cast. This certifies
the proposed dyadic table's arithmetic budget. It does **not**, in isolation,
prove that the table encloses the original analytic factors.

The reviewer also inspected the pointwise-to-table conversion pattern at
`FactorBounds/Sigma001` and the last indices of `FactorBounds/Height030`.
Each case fixes the actual `Fin` index, invokes the corresponding analytic
enclosure, and reduces that same index's list entries to `c/2^48` and
`a/2^48`. In particular the last height row 987 is retained. The aggregator
`M2PilotFactorBounds` dispatches sigma indices by division by 128 (12 blocks)
and height indices by division by 32 (31 blocks, with the actual final
index bound 988). Its source covers the required finite domains. This
sampling is not a claim of independent inspection of every generated case,
nor of completed compilation of all 43 blocks.

At this stage the root reports the integer certificate and the auxiliary,
prime-power, and trivial numerical bounds have passed their individual kernel
builds. The complete factor-module build and aggregation are still in progress.
**M2 remains PENDING** until those enclosures, the resulting complete-budget
inequality, and the final theorem/dependency evidence have been connected.

## 12. Final-result source review (compiled final evidence pending)

The reviewer has read `M2PilotResult`, `M2PilotLowRankBound`, and
`M2PilotSmallBudgets`. These were not implemented by this reviewer. The source
of the final assembly discharges `completeBudget < 1`; it does not move that
premise into a differently named parameter. The main bound passes through
`lowRankTaylor20_mono`, all four actual pointwise-to-dyadic factor bounds, and
the exact dyadic integer certificate. The auxiliary, actual prime-power,
and actual trivial-zero budgets are then added.

The displayed arithmetic agrees exactly with the human mathematical note:

```text
3759/4000 + 1/50000 + 1/1000000 + 1/1000000
  = 234943/250000
  = 469886/500000
  = 0.939772
  < 47/50
  < 1.
```

`234943/250000` is a non-strict upper bound; `47/50` is the strictly larger
convenient cutoff. The two are not equal. The strict slack to `47/50` is
`57/250000`, while the slack to one is `15057/250000`. The actual final source
uses the correct inequality directions.

The source statement of `pilot_short_interval_from_inputs` has precisely
`QRHSevenEighths`, `CSv2`, `RosserZeroCount`, `IntegratedExplicitFormula`, and
the positive-x/closed-log-cell domain. In particular it has no numerical,
weighted-zero, finite-height RH, CHJII, or local-prime premise. Its conclusion
is the actual strict `ShortInterval6 x`, for `715/4 <= log x <= 179` only.
These source-level observations await the final compiled theorem and proof
closure evidence before a final M2 judgment.

One documentation correction was requested during comparison with
`milestone2_mathematical_note.md`: the height nodes are
`u_i=(1841+i)/64`, `0<=i<=988`, whereas the moment grid uses the right endpoints
`t_i=u_(i+1)=(1842+i)/64`, `0<=i<988`. The moment shift must therefore be written
`v_i=t_i+log(t_i)`, not inadvertently applied to the first node `u_0`.
The Lean source uses the correct right-endpoint grid. The reviewer corrected
the human note with the root agent's authorization, explicitly separating the
first kernel node from the moment heights. This notation issue is resolved;
no mathematical Lean file was changed.

## 13. Final M2 evidence and disposition

The reviewer inspected `Milestone2Dependencies.lean` and the complete recorded
output `milestone2_dependencies.txt`, including its success marker, final
theorem types, axiom reports, expanded external inputs, and the required
proof-dependency closure. The root reports this diagnostic exited successfully
in approximately 24 seconds after successful compilation of `M2PilotResult`.
The recorded marker is `MILESTONE2_REQUIRED_PROOF_DEPENDENCIES_PRESENT`.

The final printed theorem is:

```text
pilot_short_interval_from_inputs
  (HQ : QRHSevenEighths) (HC : CSv2) (HR : RosserZeroCount)
  (HF : IntegratedExplicitFormula)
  (x : Real) (hx : 0 < x)
  (hlo : 715/4 <= log x) (hhi : log x <= 179)
  : ShortInterval6 x.
```

There is no numerical-budget parameter. The separately printed theorem
`completeBudget_le` has no hypotheses and concludes
`completeBudget <= 234943/250000`. Both final theorems report exactly
`[propext, Classical.choice, Quot.sound]`. The final audit contains neither
`sorryAx` nor `Lean.ofReduceBool`. The four literature statements remain
explicit theorem parameters, not hidden custom axioms or conclusions claimed
to have been proved from nothing.

The dependency diagnostic checks that the final proof uses the actual factor
bounds in all four families, the exact rational integer certificate and its
real-sum bridge, the Taylor bound, all auxiliary/small-budget results, and the
entire analytic chain previously reviewed. Its closure also includes the actual
weighted Mangoldt identity, the classical height-limit application, genuine
zero multiplicities and conjugation, the full geometric residual, the actual
prime-power bound, and strict `Nat.Prime` extraction. Thus the final theorem
is not merely a renamed conditional criterion with an unproved local budget.

The reviewer also inspected `m2_pilot_numeric_build_2026-11-06.json`, recorded
at `2026-11-06T05:43:32.817464+00:00`, and checked its source hashes against the
current files. All **122** entries in its numerical-chain source manifest
match in both byte length and SHA-256. Both recorded block families contain
43 successful builds (43 enclosure modules and 43 factor-connection modules);
the reviewer separately checked their source hashes and exit codes. The final
factor aggregator, actual low-rank bound, and numerical axiom diagnostic have
successful assembly records. The record also contains successful read-only
regeneration comparisons; the reviewer did not rerun the generators.

The numerical record explicitly distinguishes the first enclosure batch's
Lean default `autoImplicit=true` from later factor and assembly commands using
`-DautoImplicit=false`. The generated theorem binders are explicit. The final
printed theorem type and dependency audit are the evidence for the absence of
unintended mathematical parameters. The complete numerical axiom audit reports
only the same standard three axioms.

All **28** module hashes already listed in this review were rechecked and
match the current source. This includes `M2PilotResult` and the budget-identity
and integer-moment modules. The human note's right-endpoint indexing correction
is recorded in Section 12. Its rational total agrees with the final Lean bound.

**Build scope:** this M2 completion uses the newly compiled modules, successful
incremental final assembly, and the final dependency/axiom audit. The reviewer
did not personally rerun these aggregate commands. This was **not** a new clean
build of every ancestor or every module in the enlarged repository. The earlier
58-module whole-library build report belongs to **M1**, and is not presented
as an M2 whole-library build. A later clean reproducibility build remains a
separate validation step; it is not falsely reported here as already performed.

**Final judgment: M2 PASS**, for the single fixed difficult cell and the exact
four external inputs above. For every positive real x satisfying
`715/4 <= log(x) <= 179`, the completed formal theorem produces a natural prime
strictly between `x` and `x + 6*x^(5/6)`. The budget is bounded by `0.939772`,
strictly below `47/50` and one. No unresolved local analytic or numerical premise
remains in this pilot theorem. The remaining intervals and global assembly
belong to milestone 3; **the full k=6 theorem is not certified by this report**.

## Source snapshot

SHA-256 values below identify the reviewed source snapshot. The addendum includes the subsequent budget identity and conditional pilot
assembly. Later source changes require an appended review.

| Module | SHA-256 |
|---|---|
| `FiniteDensityGrid` | `e7788c6da80ab537a88156ac6c36296b3d8eca1949b6929359b65cfd70f8a572` |
| `HeightKernel` | `c893a43e9242f7a64b05903cd20a94f27f3a2e72157c25e221a3463c47742f6f` |
| `HeightGrid` | `eb181da69aaa4a7003af3182a3a313bddb240b33baa819a018ae22f4b5ce5c6c` |
| `GeometricHeightTail` | `37506523d5c8384c77cd7adf51b7135d2b60e438afff52bb0ee4a6c9a07aec8f` |
| `DensityGridGrowth` | `0aeba9712309446cab2eb070d02fca8cc350e101ad8e6844b59912074188ca87` |
| `TrapezoidKernel` | `b970b79fe41f4afde356ce7598d28d377e10c4178791c0bff88f0125c89467a3` |
| `TrapezoidTrivial` | `7c9bfaae3b762dac8508e083a82bbe556051c1f173c3dad98885bde01f80868e` |
| `TrapezoidZeroBound` | `7780c830dda9d4164172395d60031f25ef1e8c56da66e2c3e98eb4163701b27f` |
| `TrapezoidHeightBound` | `fcd0ba6678a162cbfbd6535bcb978947adc15651d2eeb5d8f201518966a8b152` |
| `IntegratedPsi` | `52a735da07c58adfaee31f0405079c55879ef63585bf60d7b43e4359ca658245` |
| `IntegratedExplicitFormula` | `9dfad65f0a4a3849e4f89f6aca7b0f25511a2958466e1bd2712845d8e368aced` |
| `MiddleDomains` | `3d828ba99a09181bdc1b4c47c643bfa86129f38f0b7fb228977f2d98046c06c5` |
| `TrapezoidPrime` | `646a9d2888d043f3b824ab1de5d702c9f2f66a755ed2653fa5fbbbbf8a5a4c3b` |
| `M2PilotGrid` | `676dc754c70e9ef926b8748faf03db726abd5ee739a9c6eebebfeebd737271ea` |
| `M2PilotExpression` | `c63d9903159f97c953c1c744bac2288e52fa2d58b182a9bdafd6fcd66c91881d` |
| `M2PilotBudgetDefinitions` | `d495da05eff262db0bc8e778a6aeb24df3c1febfe6ad895c546861eb8b49a71d` |
| `M2PilotBudgetIdentity` | `55295f85a8b204e3362c7b30307ff32d33e209eb0a229b2e6dc0288ce688250c` |
| `M2PilotAnalytic` | `2870605a230c4b910e2094dc6ab0883abbbaba09f468463ba8a740b957193428` |
| `TrapezoidCell` | `be9f5069f595423f3b808fc84b68aa3637ccdc643229056cfaad88e1a6eecc86` |
| `TrapezoidGridCell` | `636274c7bd8348dd95506a0f10320427ac7d408dc73d5601bcc0e5e31f9bd20d` |
| `LowRankTaylor` | `899c71a212974dd6dd18bad7eb8636a7f0d0d0f426f66a160fa986f41c9269e5` |
| `LowRankInteger` | `7a40f7398f9b37e6cfb89065ce4b9eadd36d66477538deb8d55faf2ccb322c77` |
| `M2PilotIntegerData` | `33121bf8c5c3d7290535a845d5b2432f83dea3c022ea81db09d8cabd8f468fce` |
| `M2PilotIntegerCertificate` | `9f4daf3fb0cd397f6d2a851d46cc51a0f2b47b8808e177c56846dabc2f319df8` |
| `M2PilotFactorBounds` | `7625778d79d2e11722125c556ff65bcd1a273fb7184a648693d5c9255432883b` |
| `M2PilotLowRankBound` | `1bbffe9fbcc5e5d7c261b0898b866e688c6d8d9ab4e84d40ff3055cc4f9eca41` |
| `M2PilotSmallBudgets` | `99303748ae604303d915b73720d043efc5c89b5bfda1e9e3c6b5a2fd59c54e64` |
| `M2PilotResult` | `e3c045d6064d180117f6bb6b2010ecd084f83e0172c1c1969ec68b34d8400066` |

Diagnostic evidence SHA-256:

- `Milestone2AnalyticDependencies.lean`: `ecf4ec503b99b38f1a9a22fdd59a592bae3f698cd08ab10690bbc917dfc726dd`.
- `milestone2_analytic_dependencies.txt`: `898bdf1ca50e5e50f25e7261f21e4acab9857e8e4e20503d8c51be62492cfc6f`.
- `Milestone2Dependencies.lean`: `0879f78c2170a6e3ed3bf50c1d8fcf84b8d0a2ea5b38f8b7e49734bb12fc5e2a`.
- `milestone2_dependencies.txt`: `0570bbe798b4cc4bfe451b857b124dde64700e8557747fbadf7ccea7f74b0e7a`.
- `m2_pilot_numeric_build_2026-11-06.json`: `e71daaec377fa0e788f740d36404194273be402f03f82df7efb7dcb1e425c7ac`.

[hildebrand]: https://eclass-b.uoa.gr/modules/document/file.php/MATH717/04.%20%CE%92%CE%BF%CE%B7%CE%B8%CE%AE%CE%BC%CE%B1%CF%84%CE%B1/Analytic-number-theory-Hildebrand.pdf
