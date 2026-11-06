# Round 2: density envelopes for the fourth-power middle range

Date: 2026-11-06. The conclusion of the actual scan is negative but quantitative: the source-checked improvements below reduce the present smooth absolute-zero bound by about 5–8% on (110\le L=\log x\le150), not by orders of magnitude. They leave the principal obstruction intact. All reported integrals in this file are **floating-point exploration**, not certified interval inequalities or lower bounds on the actual prime-counting error.

Owned artifacts: `code/density_envelope_round2.py`, `results/density_round2.json`, `results/density_round2.csv`, and `results/density_round2_refined.json`. The script reads the existing `smooth_scan.py` kernel functions, without modifying them or any previous certificate.

## Admitted source inputs

The first input is [Chourasiya–Simonič, arXiv:2507.15184v2](https://arxiv.org/html/2507.15184v2). In addition to its Corollary 1 already used in the project, Appendix equation (119) gives

\[
D_{119}(\sigma,T)=A T^{\frac83(1-\sigma)}(\log T)^{6-4\sigma}
+B(\log T)^2,\qquad N(\sigma,T)\le D_{119}(\sigma,T),
\]

for (T\ge H=3\cdot10^{12}), on the closed sigma rows in Table 4. The eight applicable rows are:

| Sigma interval | A | B |
| --- | ---: | ---: |
| [0.625, 0.65625] | 2.900 | 5.027 |
| [0.65625, 0.6875] | 3.474 | 4.789 |
| [0.6875, 0.71875] | 4.149 | 4.536 |
| [0.71875, 0.75] | 4.940 | 4.296 |
| [0.75, 0.78125] | 5.860 | 4.042 |
| [0.78125, 0.8125] | 6.925 | 3.800 |
| [0.8125, 0.84375] | 8.148 | 3.546 |
| [0.84375, 0.875] | 9.543 | 3.301 |

The envelope takes the pointwise minimum with the actual Corollary 1 row, not with a uniform overestimate. No Appendix row is extended to smaller sigma.

The second input is [Bellotti–Wong, arXiv:2412.15470v2, Theorem 1.1](https://arxiv.org/html/2412.15470v2). Put

\[
P(T)=\frac{T}{2\pi}\log\frac{T}{2\pi e},\qquad
R(T)=\min\{0.10076\log T+0.24460\log\log T+8.08344,
0.11200\log T+0.12567\log\log T+3.77417\}.
\]

It gives (|N(T)-P(T)|\le R(T)) for (T\ge e). Conjugation across the critical line therefore gives the valid local estimate, for (T_1\ge T_0\ge e), (\sigma>1/2),

\[
N(\sigma,T_1)-N(\sigma,T_0)
\le\frac{P(T_1)-P(T_0)+R(T_1)+R(T_0)}2. \tag{1}
\]

This subtracts a **lower** bound at (T_0) from an upper bound at (T_1). It does not subtract two cumulative density upper bounds. Taking (T_0=H), where finite RH gives (N(\sigma,H)=0), makes (1) a further cumulative cap above (H). At (T=H) the off-critical count is separately set to zero. The script evaluates the main-term difference with `expm1`, avoiding subtraction of nearly equal large floating-point numbers.

Finally, sigma monotonicity permits a modest row-boundary correction: for every previously passed source-row endpoint (s\le\sigma), (N(\sigma,T)\le N(s,T)\le D(s,T)). At an endpoint the script deliberately evaluates the constants from the closed row on its left. This eliminates artificial upward jumps caused by changing row constants. It is a legitimate minimum of upper bounds; it does not differentiate or subtract them.

## What the computation did

For each mode it uses the same (M=2,3,4) nonnegative beta kernels and Mellin derivative envelope as `smooth_scan.py`, including the bounded-variation last derivative and analytic height tail. The symmetry layer factor is retained. The four modes are:

| Mode | Bound used |
| --- | --- |
| `cs2` | Original CS v2 row bound and half-total count |
| `envelope119` | Also minimize with equation (119) |
| `envelope_hcap` | Also minimize with (1), starting at H |
| `envelope_monotone` | Also use earlier source-row endpoints |

The integration splits every source-row boundary and the finite-RH height. Extra log-height cuts at distances (10^{-8},10^{-6},10^{-5},10^{-4},10^{-3},10^{-2},10^{-1}) above (\log H) help resolve the narrow region in which (1) matters. The default run uses 20-point height and 16-point sigma Gauss rules and log-height cells of length at most 1. Stored results include every tested kernel and a row-by-row breakdown. Refinement checks change these parameters together; they are numerical consistency checks, not quadrature error certificates.

Representative results, choosing the best of the three tested kernels in each mode:

| L | Best M | CS v2 delta | + Appendix 119 | + local cap | + row monotonicity |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 110 | 3 | 593.303 | 553.540 | 549.999 | 549.027 |
| 115 | 2 | 3207.238 | 2982.302 | 2977.671 | 2972.730 |
| 120 | 2 | 2957.511 | 2756.071 | 2755.943 | 2751.645 |
| 130 | 2 | 2334.065 | 2186.160 | 2186.152 | 2183.171 |
| 140 | 2 | 1817.703 | 1709.779 | 1709.778 | 1707.750 |
| 150 | 2 | 1399.499 | 1322.109 | 1322.109 | 1320.751 |
| 300 | 2 | 12.9151 | 12.6913 | 12.6913 | 12.6898 |
| 375 | 2 | 0.941283 | 0.933887 | 0.933887 | 0.933839 |
| 400 | 2 | 0.384611 | 0.382255 | 0.382255 | 0.382240 |

The small differences in the last displayed digits are quadrature sensitive. For example, with height order 32, maximum step 0.4, and sigma orders 32, 64, 128, `envelope_monotone` at (L=120,M=2) is respectively 2752.170105, 2752.049957, and 2752.067878. At (L=150) the corresponding values are 1320.886604, 1320.850503, and 1320.857715. The size and sign of the improvement are stable; no value near 1 is being promoted to a theorem.

At (L=120,M=2), the Appendix improvement occurs almost entirely in the rightmost sigma row:

| Sigma row | CS v2 layer | With Appendix 119 | All admitted improvements, default quadrature |
| --- | ---: | ---: | ---: |
| [0.71875, 0.75] | 3.31708 | 3.31708 | 3.23798 |
| [0.75, 0.78125] | 20.27075 | 20.27075 | 20.24492 |
| [0.78125, 0.8125] | 109.93278 | 109.93278 | 109.79042 |
| [0.8125, 0.84375] | 532.44160 | 532.44160 | 531.72747 |
| [0.84375, 0.875] | 2291.30445 | 2089.86511 | 2086.44975 |

Thus even eliminating the rightmost layer altogether would leave a large budget. Equation (119) does not provide the simultaneous large improvement through the lower sigma rows that would be required here.

## Why the local cap does little

At (\sigma=7/8,T=1.01H), the CS row gives approximately (7.97012\cdot10^8), Appendix (119) gives (6.11461\cdot10^8), while the valid local count cap is (6.42112\cdot10^{10}). The latter is weaker. At (T=1.000001H), however, the local cap is about (6.41994\cdot10^6), so it does win very close to (H).

The numerically located crossover with the minimum of the two density bounds is:

| sigma | T/H at crossover | Absolute height width T−H |
| ---: | ---: | ---: |
| 0.80 | 1.0207832475 | (6.23497\cdot10^{10}) |
| 0.85 | 1.0007946003 | (2.38380\cdot10^9) |
| 0.875 | 1.0000948503 | (2.84551\cdot10^8) |

Near the most expensive right edge, it improves only a very narrow relative height band. This explains its small integrated effect. These numbers concern competing admissible upper expressions; they say nothing about how many off-critical zeros actually exist.

## Cho24 and the ambiguous comparison sentence

The cited [Chourasiya, arXiv:2412.02068v1 PDF](https://arxiv.org/pdf/2412.02068v1) was checked directly. Its Theorem 1.1 states a Carlson-shaped (K(\sigma,T_0)T^{4\sigma(1-\sigma)}(\log T)^{5-2\sigma}) bound. Table 1 only supplies sigma values 0.60–0.66, not 0.80–0.875. Moreover, the proof on pages 7–8 has logarithmic powers 3 and 4 in (4.5)–(5.3), and its displayed (K(\sigma,T_0)) still contains (T). The theorem and those proof lines therefore require reconciliation before independent certification. No unsupported constant 0.78 is applied throughout the critical strip.

The code evaluates the literal H-height table rows at 0.60 and 0.66 only as diagnostics, extending them to larger sigma by count monotonicity. They are far larger than the admitted envelope in the target band; for sigma 0.875 and (T=1.01H), that diagnostic is about (1.03\cdot10^{16}). Cho24 is **not included in any scan envelope**.

The CS v2 introduction's word “latter” should not be read as evidence of an unreported high-sigma Cho24 improvement. A quantitative check identifies the likely referent as the second CS bound: at sigma (7/8), its main-term ratio to (119) is

\[
\frac{21.77}{9.543}(\log T)^{-1/6}.
\]

Its crossing is (\log_{10}T=(21.77/9.543)^6/\log 10=61.2104176\ldots), consistent with the text's sufficient threshold (10^{61.3}). The Carlson height exponent is instead (7/16), larger than (1/3), so it cannot have the stated eventual improvement direction. This is an inference from the formulas, not an additional density theorem.

## Search for more powerful explicit exponents

The primary-source follow-up did not identify a ready-to-use Huxley, Jutila, or Bourgain bound with all numerical constants and a validated starting height appropriate to this target band. This is a bounded search result, not a claim that no such theorem exists.

For comparison, [Bellotti, arXiv:2405.12545v2](https://arxiv.org/html/2405.12545v2), Theorem 1.1 and Table 2, supplies explicit log-free estimates only for tabulated sigma thresholds at least 0.985. Its remark discusses extension to smaller sigma when (T>\exp(90)), without providing the needed table for the present band. These published rows cannot be extrapolated down to 0.80–0.875. Its introduction states the stronger Huxley/Bourgain-type exponent results in big-O form; those exponents alone provide no usable numerical constant here.

The same paper's Lemma 2.1 and Corollary 2.3 do give local disk counts near the 1-line. They constrain very narrow windows, but they do not directly supply an accumulated off-critical population bound substantially smaller than the source-checked envelopes evaluated here. They have not been silently substituted into the scan. Obtaining a useful new local density theorem, or explicitly tracking constants through a stronger exponent method, remains new analytic work.

## Reusable interfaces

```python
import density_envelope_round2 as density

# N(sigma,T) envelope in log scale; NumPy broadcasting is supported.
log_D = density.log_density_bound(sigma, log_T, mode='envelope_monotone')

# Right-of-critical-line count in (exp(u0),exp(u1)], for sigma>1/2.
cap = density.local_count_cap(u0, u1)

# Standalone diagnostic using the existing smooth kernel, without mutation.
result = density.smooth_bound(L=120, M=2, mode='envelope_monotone',
                              height_order=32, sigma_order=128, max_step=.4)
```

`cs2_log` and `appendix119_log` expose the individual sources; they reject heights below (H). `appendix119_log` returns infinity outside its sigma domain within the surrounding scan range. `cho_table_log` is diagnostic only. The normal script invocation recreates only its `density_round2` result files. The JSON records the script hash and the imported kernel-script hash, all constants, scan settings, row budgets, and local-cap crossover diagnostics.
