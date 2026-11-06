# A new trapezoid certificate for the fourth-power far segment

Date: 2026-11-06. Implementation: Codex sub-agent `lean_prime_power_budget`,
using the previously formalized analytic and integer-moment modules. This note
is an implementation record, not independent peer review.

## Relationship to the historical result

The original far segment covers `400 <= log(x) <= 700` using sixty cells and
a polynomial smoothing kernel. The new Lean development uses the already
proved four-point trapezoid kernel with `a=1/32`, `b=31/32` instead. It proves
the same kind of actual `ShortInterval4` conclusion. It does not assert that
the historical polynomial-kernel calculation has been translated line by line.
The old manuscript, code, results, and frozen certificates remain unchanged.

The genuine zeta-zero kernel, density grid, complete geometric residual,
actual integrated von Mangoldt identity, prime-power removal and strict prime
extraction are reused. The explicit external inputs are `QRHSevenEighths`,
`CSv2`, `RosserZeroCount`, and `IntegratedExplicitFormula`.

## New pilot and its actual numerical expression

For the pilot take `A=400`, `C=1601/4`, `x=exp(L)`, `h=4 exp(3L/4)` and
`q=1+exp(C/4)/4`. The real-part nodes are `(512+j)/1024`, with 384 cells,
and the log-height nodes are `(795+i)/8`, with 125 cells ending at `U=115`.
The first height satisfies the CS threshold and lies in the flat part of
the kernel. The height factors use the right endpoints `(796+i)/8`.

The kernel is `min(1,(64/31)q/T,(4096/31)q^2/T^2)`. The final height
coefficient includes the doubled geometric residual
`32*(4096/31)*q^2*exp(-2U)*Phi_A(U)`, including residual contributions from
zeros below the last node. The actual normalized prime-power budget is

```text
(32/31)*sqrt(1+4 exp(-A/4))
  *(C+log(1+4 exp(-A/4)))^2/(8 log 2)*exp(-A/4).
```

The trivial-zero budget is `exp(-3A)/(1-exp(-2A))`.
`M3FarBudgetIdentity` proves exact equality between these analytic expressions
and the complete finite numerical expression.

The factorization uses shifts `p0=1/3`, `v0=104`. The sigma and height powers
are nonnegative and bounded by `2/3` and 16, so their products are at most 11.
This permits reuse of the proved degree-20 Taylor majorant and its doubled
21st remainder. Both entries of each integer row use denominator `2^48`.
The height-factor witnesses include an additional outward padding of
`1048576/2^48`; every resulting enclosure is independently proved by Lean.

The kernel-checked main moment bound is `9/20`. The auxiliary term is at most
`1/50000`, and each of the prime-power and trivial-zero terms is at most
`1/1000000`. Thus the proved total is

```text
completeBudget <= 225011/500000 = 0.450022 < 1/2 < 1.
```

Arb exploration estimated about `0.434199143` before the dyadic/Taylor
majorant; that exploratory value is not the formal certificate bound.

## Validation and extension

All 16 analytic enclosure modules, all 16 table-connection modules, the exact
integer certificate, the factor aggregator, and `M3FarResult` compiled with
native Lean. The final pilot theorem has only the four named external inputs
and `x>0`, `400 <= log(x) <= 1601/4`; it contains no numerical-budget premise.
Its axiom report contains only `propext`, `Classical.choice`, and `Quot.sound`.
See [numeric build evidence](m3_far_numeric_build_2026-11-06.json) and
[printed theorem and axioms](m3_far_kernel_axioms.txt). This is an incremental
build record, not a new clean rebuild of all ancestors.

The three new `generate_m3_far*` scripts support read-only `--check`; those
checks match the emitted sources. The published arithmetic data are witnesses,
not assumed estimates or imported Arb success flags.

Extending this pilot to the whole original far range uses the separately
implemented height/density translation theorem and `M3FarUpper`. Uniform actual
prime-power and trivial-zero bounds are supplied by `FarUniformBudgets`.
That assembled range theorem has its own validation; the pilot alone is not
a claim of the full k=6 result.
