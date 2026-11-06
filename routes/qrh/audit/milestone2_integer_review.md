# Milestone 2: analytic kernels, auxiliary budget and integer evaluation

Date: 2026-11-06. This is an implementation self-review by the Codex worker
that wrote the modules below, not an independent mathematical referee report.
It records completed module checks; the root integration audit records the
scope and external hypotheses of the assembled milestone theorem.

## Compilation and arithmetic method

Every module listed below was compiled individually with exit code 0 using
Lean 4.36.0-rc2 and the project's pinned Mathlib revision
`9d581dfff2e41de989072ea63abf3daf69311520`. The actual command pattern was:

```powershell
& ./routes/qrh/code/run_lean.ps1 `
  -File LegendreK6/<module>.lean `
  -DependencyRoot D:/UGit/AI4Math/legendre_k67/proof/LegendreK67/.lake/packages `
  -LeanExecutable C:/Users/Bernkastel/.elan/bin/lean.exe
```

The absolute cache and executable paths describe this local run, not a public
dependency requirement. The driver uses `lean -o` and the pinned package cache;
it does not run a native decision procedure. Successful individual runs were
reported in the session tool output. Temporary signature/axiom audit modules
were compiled with the same command under `lean/.lake/tmp`; those temporary
modules are not publication sources. The persistent integration evidence is
[milestone2_kernel_axioms.txt](milestone2_kernel_axioms.txt) and
[milestone2_analytic_dependencies.txt](milestone2_analytic_dependencies.txt).

| Module | Result and relevant scope |
|---|---|
| `TrapezoidKernel` | Three actual complex-power four-point bounds: base, inverse-height and inverse-square-height. The base bound also applies to negative even real zeros. |
| `TrapezoidTrivial` | Actual primitive series summability, exchange with the four-point operator, and norm bound `h*x^(-3)/(1-x^(-2))`, for `x>1`. |
| `TrapezoidZeroBound` | Actual finite multiplicity-weighted zero sums, conjugation factor 2, and prefix comparisons. No weighted-zero estimate is assumed. |
| `TrapezoidHeightBound` | Density-grid and geometric-tail bounds from explicit QRH, CS v2 and Rosser hypotheses plus ordinary grid-domain obligations. |
| `M2PilotAuxiliary` | Exact telescoping of both grid weights; total height coefficient at most 4000; final auxiliary budget at most `1/50000`. |
| `M2PilotIntegerData` | Literal 1536-row and 988-row natural-number pair tables, length proofs and Fin reindexing. Data alone do not assert analytic enclosure correctness. |
| `M2PilotIntegerCertificate` | Exact rational low-rank value at most `3759/4000`, converted to the real finite-sum bound `dyadicLowRank20_le`. |

The auxiliary scalar estimates use `dyadic_interval [prec := 64]` on explicitly
cast rational constants. The integer certificate uses `decide +kernel` with
`maxRecDepth 100000` and `maxHeartbeats 0`. This option asks Lean's kernel to
check reduction directly; it is not `decide +native`, `native_decide`, or
`Lean.ofReduceBool`. Ordinary elaborator-mode `decide` was first tried and
failed to unfold `Rat.div`, even on the small test `(3759/4000 : ℚ) ≤ 1`.
Kernel mode proved the complete ground inequality. No externally calculated
moment or successful-program status appears among its theorem parameters.

Individual `#print axioms` checks for the final kernel, trivial-series,
actual-zero, height-budget, auxiliary and integer results returned only
`[propext, Classical.choice, Quot.sound]`. The two table-length proofs require
no axioms. The auxiliary and integer numeric bounds have no theorem premises.
No listed source contains `sorry`, `admit`, an added `axiom`, `native_decide`
or `Lean.ofReduceBool`. Standard-axiom auditing is supplemented by the explicit
premise checks above; it is not a substitute for them.

## Read-only regeneration

`generate_m2_integer_data.py` reuses the current `sigma_data` and `height_data`
proposals: 48-bit scaling, height-factor padding 65536 integer units, and
height-power padding 1 unit. Arb only proposes integer witnesses. The separate
factor-enclosure modules prove their relation to the actual real expressions.

The generator now supports `--check`: it builds proposed UTF-8 bytes in memory,
compares them with the existing Lean file, and returns failure on mismatch or a
missing file. It does not call any output-write operation in check mode.
The following run completed with exit code 0 and `CHECK_PASS`:

```powershell
python -B routes/qrh/code/generate_m2_integer_data.py --check
```

The data file's SHA256 and `LastWriteTimeUtc` were checked before and after this
run and were unchanged. Output: 76543 bytes, 1536 sigma rows, 988 height rows.
The exploratory decimal `0.9397325391772179` printed by the generator is not
the proof: `rationalLowRank20_le` is the kernel-checked exact rational result.

## Frozen source hashes

All SHA256 values were read from the final source bytes after successful
compilation. This review and the generator's new check option do not change
any frozen Lean source or table.

| Source under `lean/LegendreK6/` | SHA256 |
|---|---|
| `TrapezoidKernel.lean` | `b970b79fe41f4afde356ce7598d28d377e10c4178791c0bff88f0125c89467a3` |
| `TrapezoidTrivial.lean` | `7c9bfaae3b762dac8508e083a82bbe556051c1f173c3dad98885bde01f80868e` |
| `TrapezoidZeroBound.lean` | `7780c830dda9d4164172395d60031f25ef1e8c56da66e2c3e98eb4163701b27f` |
| `TrapezoidHeightBound.lean` | `fcd0ba6678a162cbfbd6535bcb978947adc15651d2eeb5d8f201518966a8b152` |
| `M2PilotAuxiliary.lean` | `458154518e8180d64adbfc5c8f4b9269b26661c653f2b0551619a7a3c0e83497` |
| `M2PilotIntegerData.lean` | `33121bf8c5c3d7290535a845d5b2432f83dea3c022ea81db09d8cabd8f468fce` |
| `M2PilotIntegerCertificate.lean` | `9f4daf3fb0cd397f6d2a851d46cc51a0f2b47b8808e177c56846dabc2f319df8` |

Generator `code/generate_m2_integer_data.py` after the read-only option:
`081ff1fc3d801ca9dc1ebfe077873ec51e63bee02534c538cfc40073bc557083`.

A later temporary List.get performance comparison was stopped at the numerical
worker's request to release compilation resources. It produced no complete
timing result and motivates no correctness or performance claim. It changed
none of the sources or data listed above.
