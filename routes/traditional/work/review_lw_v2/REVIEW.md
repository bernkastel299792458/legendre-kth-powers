# Referee report: v2 height-dependent Littlewood region (`phase1_littlewood/zfr_local_v2.csv`)

**Object.** `zfr_local_v2.csv`, sha256 `ceacbca5…288d345` (matches REPORT §11.2). It has 366 bands over log t ∈ (28.73, 6 006 998], with Z₂ ∈ [11.683, 19.681], all marked `proved`.

**Code and documentation.** Produced by `cert_v2.py` with `zl_core.py` and `cert_profile.py`, and documented in REPORT §11.

**Scope.** Only what is new relative to v1, which was reviewed in `phase1_littlewood/review/REVIEW.md`. The v1 mathematics (thesis method, R1–R7, Claim W, λ-limit, assembly of (★)) is taken as reviewed there.

**Rules.** No file outside this folder was modified. Every script here runs with `python -I <script>`.

## Verdicts

| # | Item | Verdict |
|---|---|---|
| 1 | New inputs: statements, ranges and hypotheses | **CONFIRMED** |
| 2 | Extension to log t ≈ 6·10⁶; is Z₂ ↓ 11.7 plausible? | **CONFIRMED.** Reproduced independently; consistent with the method's asymptotics and with the literature |
| 3 | Certification code for the new ranges (coverage, float leaks, the 1.6e-8 cell) | **CONFIRMED.** The 1.6e-8 is a reporting artefact, not a near-failure |
| 4 | Monotonicity and other caveats for downstream use | **CONFIRMED with caveats** (§4). Nothing wrong in the file; consumers must respect them |

**No FATAL or MAJOR issue was found.** `zfr_local_v2.csv` can be used as an input, with tier "own proof (thesis method, unrefereed) + refereed inputs only", under the caveats of §4.

## 1. New inputs

| Input | Exact statement (source text checked) | Use in v2 | Check |
|---|---|---|---|
| Yang, JMAA 534 (2024), Thm 1.1 (`sources_zfr/2301.03165.txt` l. 63–65) | "Let k ≥ 4 be an integer and σ_k := 1 − k/(2^k − 2). Then \|ζ(σ_k + it)\| ≤ 1.546 t^{1/(2^k−2)} log t, t ≥ 3." §5 (l. 3247) restates that it holds uniformly in k ≥ 4 and t ≥ 3 | lines n = 4…18 are allowed in `zl_core.LINES`; the CSV actually uses n ≤ 14 (n = 11–14 above log t ≈ 10⁵) | `LINES[n] = (1 − n/(2ⁿ−2), 1.546, 1/(2ⁿ−2))` is exact. Yang's own Littlewood proof uses k = k(t) → ∞ (his Lemma 4.2), which is exactly this usage |
| Thesis Lemma 3.7 (pointwise bound to integral bound), hypotheses | 0 < δ ≤ ½, t ≥ 1000, ½ ≤ σ ≤ 1 − 1/t, bound for y ≥ t/2 with Z ≥ ½ | δ = 2λ/π ≤ 1/π; T = kt ≥ e^{28.7}; σ_n ≤ 1 − 18/(2¹⁸−2) ≪ 1 − 1/T; Z = 1 | all satisfied for every line and every t in the bands |
| Bellotti, arXiv:2306.10680v1 Thm 1.2 (journal JMAA 536 (2024) prints 53.989) | ζ ≠ 0 for \|t\| ≥ 3 and σ ≥ 1 − 1/(54.004 (log\|t\|)^{2/3}(loglog\|t\|)^{1/3}) | window above V₁ only, i.e. the last ≈ 2.77 in v of the top band | Littlewood form Z_VK(v) = 54.004 (log v)^{4/3} v^{−1/3} is exact. It is decreasing for log v > 4, so Z_VK(log u) ≤ Z_VK(V₁) for all log u > V₁. The code uses Z_VK(V₁) + 10⁻²⁰ = 11.58828777451843944029 against an exact value of 11.58828777451843944028 (`window_check_output.txt`). The 54.004 statement is implied by the journal's 53.989 |
| MTY (unchanged), with V₀ = 28.73 | ζ ≠ 0 for σ ≥ 1 − 1/(5.558691 log\|t\|), \|t\| ≥ 2 | window below V₀ | Z_eff = 5.558691·log 28.73 = 18.666 < 18.922 |
| Ford's W₀ bound (thesis Lemma 2.3, with corrected c₀ = 1/(sin θ cos³θ)) in a **new regime** | \|W₀(z)\| ≤ C(ν, r)\|z\|⁻³ for Re z ≥ ν, \|z\| ≥ r | v2 uses r = ν = λ/η ≈ 1.4·10³–7·10³ in the zero sums (v1: ≤ 282), and r ≈ 10⁶ in the E-terms | `ford_large_r.py`: W₀ is computed by its convergent integration-by-parts series, checked against quadrature. Max ratio \|z³W₀\|/C = 0.99833 (r = 1400), 0.99922 (3000), 0.99967 (7000), 0.99998 (10⁵). On Re z ≥ r = 10⁶ and 3·10⁶ it is 0.9999975 and 0.9999992 |

**Structural remark on Ford's bound.** It is asymptotically **exact** in its leading terms:
- c₀c₃ = |w″(0)| = 45.8677…
- c₀c₂ = w‴(0) = −w‴(d) = 106.478…

Both identities hold to 50 digits. So the bound holds with relative slack ≈ 2.31/r only.

This is not a defect, since the bound is a published lemma and holds. But it confirms that the corrected c₀ is essential: the thesis's printed c₀ = csc θ sec²θ gives c₀c₃ = 19.69 < 45.87, and the bound would then be false for large |z|.

## 2. Large heights and plausibility of Z₂ ↓ 11.7

**Independent reproduction.** `indep_v2.py asym` is the same inequality written from the mathematics, with lines n ≤ 30 and no window or rounding. It gives the local requirement:

| log t | 10³ | 10⁴ | 10⁵ | 10⁶ | 2.4·10⁶ | 6·10⁶ | 10⁷ | 10⁸ | 10¹⁰ | 10¹² |
|---|---|---|---|---|---|---|---|---|---|---|
| this method (independent) | 17.02 | 14.62 | 13.05 | 12.19 | 11.93 | 11.69 | 11.50 | 11.19 | 10.88 | 10.74 |
| CSV band containing it | 17.040 | 14.688 | 13.057 | 12.202 | 11.937 | 11.691 | — | — | — | — |
| Bellotti VK, 54.004 (Littlewood form) | 71.0 | 48.4 | 30.2 | 17.9 | 14.51 | 11.59 | 10.21 | 5.66 | 1.64 | 0.45 |
| Ford VK, 57.54 (Littlewood form) | 75.7 | 51.6 | 32.2 | 19.1 | 15.46 | 12.35 | 10.87 | 6.03 | 1.75 | 0.48 |

The CSV exceeds the bare requirement by the design factor (1 + 2·10⁻⁴), the 3-decimal rounding and the window effects, as expected.

**Why the decrease is right.** With the line σ_n, λ ≈ n/(2ⁿ−2), and the main term is ≈ (a/2λ)(v/(2ⁿ−2) + log v). Optimising n (2ⁿ ≈ v/log v) gives a width ≈ c·log v/v with c → 2G(1)/(a·w(0)·log 2). The limiting constant is therefore a·w(0)·log 2/(2G(1)) = 3.5244·5.3149·0.6931/(2·0.94269) ≈ **6.89**. It is approached extremely slowly, and the table shows exactly that.

The lines chosen in the CSV agree with the independent optimum: n = 13 at 10⁶–2.4·10⁶ and n = 14 at 6·10⁶. For n ≥ 15 the zero-sum term C·η³J·M ∝ λ⁻³ outweighs the gain in the main term.

**Literature.**
- **Yang's 21.233** (JMAA, Cor. 1.2) is a *uniform* constant.
  - His large-t argument (§4, t ≥ e^{967.6}) freezes C₂ … C₁₂ at their worst values at t₁. For example, C₂ ≤ 1.58176 versus its limit log 2.
  - His §5 says the bottleneck is small k.
  - Re-evaluating his own constants at log t ≈ 5·10⁶ gives roughly 13 (my rough estimate), so a local 11.7 from a sharper detector (Heath-Brown weight, exact G, local zero sums) is consistent.
- **Crossover with VK.** Yang states that the Littlewood region is best for e^{170.3} ≤ t ≤ e^{532141}, with VK (55.241) beyond. With local constants the crossover with Bellotti's 54.004 moves to log t ≈ 5.8·10⁶. That is where the CSV stops (V₁ = 6 006 998). Ford's 57.54 is overtaken already earlier.
- **No conflict.** Nothing in the literature conflicts with this: a Littlewood region with any constant is asymptotically weaker than VK. The thesis's 19.62 is uniform and its proof is flawed; the v2 maximum 19.681 at log t ≈ 130 is consistent with it.
- **Bellotti** has no Littlewood-type result. Her paper cites Yang's earlier 21.432.

## 3. Certification code for the new ranges

**Reproduction.** `rerun_v2.py` runs the current code and also records the argmin cell. Bands 0, 1, 102, 162, 163, 290, 309, 328, 347 and 365 reproduce `cert_v2_summary.json` exactly: cells, minrel to 10⁻¹², and lines used. This includes the three most expensive or thinnest bands (`rerun_*_output.txt`).

**Coverage.**
- Band edges are exact binary floats. All are integers except 28.73; see the caveat below.
- Initial cells share float edges and bisection shares midpoints.
- The v-ball covers [va, vb]. `ball_cover.py` tested 8784 v2-sized cells, including bisected ones, with 0 failures.

**Window.**
- `window_check.py` compares `make_zw` with an exact 50-digit window maximum. It covered 29 633 cells: the first and last 40 initial cells of every band, plus the middle one.
- 0 violations.
- The float lo/hi use a padding of 10⁻⁹·max(1, v/100), which dominates float error by ≥ 10⁴ at all heights.

**Float leaks.** None in claimed quantities.
- Floats only choose the line order, select the bands that meet a window (padded, verified above), and pick the G grid point. The grid point is protected by an exact `assert g.upper() <= mu_low.lower()`.
- G′ > 0 is certified on [0.85, 1] (old run) and on [0.849, 1] (current code). In v2, µ_low ≥ 0.936 (`misc_numbers_output.txt`), so the GTable fix is irrelevant to v2.

**Large-v behaviour (efficiency only, not rigour).**
- For v-balls of radius ≳ 0.7 at large v, arb's exp(v) in `E_bound` gives `nan` (shown in `probe_cells.py`).
- The cell then fails and is bisected. `nan` never passes, since all comparisons are false.
- This is why bands above log t ≈ 1.04·10⁶ needed 32–128 leaves per initial cell (7.4 M cells, 7.6 h).
- Choosing h0 ≤ ~1.3 above 10⁶ would avoid it. So would bounding log(T/2+4) ≤ log T and 1/(T+8) ≤ e^{−log T} without forming exp(v), as `indep_v2.py` does. COSMETIC.

**Independent re-implementation** (`indep_v2.py`).
- It uses mpmath interval arithmetic (200 bits) for ηΨ over the cell, its own w, G, a_k and Ford C, and its own window from the CSV.
- It agrees with `cell_terms` to ≤ 10⁻⁸ absolute for log t ≥ 10³, and to ≤ 5·10⁻¹² for log t ≥ 2·10⁶ (`cells_output.txt`, 32 cells).
- At small v my ηΨ is higher: by 3.5·10⁻⁵ at v ≈ 29, 10⁻⁶ at v = 130 and 1.5·10⁻⁷ at v = 300. This is fully explained by my deliberately cruder E-bound (log T instead of log(T/2+4); E ≈ 2·10⁻³ at v = 30). Margins remain positive.

**Dense point scan** (`indep_v2.py scan` → `scan_output.txt`).
- 41 points per band, plus every best-line switch located by bisection. All 366 bands, lines 3–18, exact window at each point.
- **No negative margin.**
- The worst point margin is 1.6·10⁻⁴, at the true n = 13/14 crossing v = 2 491 818.7 in band 347. The next is 1.9·10⁻⁴ at v = 30, which comes from my cruder E-bound.

**The 1.55·10⁻⁸ "smallest margin" (band (2 377 171, 2 496 030])** is the cell [2486338.696465164, 2486339.4390368853].
- I reproduced it exactly: code 1.553861·10⁻⁸ with line 14; independent iv 1.55432·10⁻⁸.
- On the same cell, **line 13 has margin 1.83·10⁻⁴**, both in the code and in my implementation.
- `cert_profile.cell_ok` returns the *first* line in the ranked order (14, 13, 12, 3, 4, 5) that passes, and reports its margin. Line 14's own margin happens to cross zero at this cell: it is −6.1·10⁻⁹ on the cell to the left, where line 13 was used.
- The same artefact explains every other "thin" margin. Each was checked on its argmin cell with the other line:

| Band | Reported margin | Margin with the other line |
|---|---|---|
| (940 728, 987 764] | 4.7·10⁻⁷ | 2.49·10⁻⁴ |
| (372 278, 390 892] | 7.9·10⁻⁷ | 2.69·10⁻⁴ |
| v1's (130, 131] | 1.6·10⁻⁶ | 2.61·10⁻⁴ (n = 3) |

- So the REPORT's (and the v1 review's) reading "where the lines cross" is inaccurate. The true robustness of every band is ≳ 2·10⁻⁵ at cell level (band 290's first cell, a window effect) and ≳ 1.6·10⁻⁴ pointwise. COSMETIC: report the max over lines in `minrel`.

## 4. Caveats for downstream use

1. **Not monotone.**
   - Z₂ rises from 18.92 to 19.681 (v ≈ 130) and then falls to 11.683.
   - At 254 band edges Z drops, so η(v) = log v/(Z v) **jumps up**. The largest jump is +0.65%, at v = 402 (18.374 → 18.255). After such a jump, η stays above its earlier value for up to 0.8% of v.
   - Use the band that contains log γ pointwise, or a running minimum. `work/v5/phi5.eta_running` already does this. `eta_piece` evaluates at the upper end of a sub-piece inside one band, which is correct because log v/(Zv) decreases within a band.
2. **Dominated parts.**
   - For v < 30.07 the bands (28.73, 29], (29, 30] and the start of (30, 31] are weaker than refereed MTY, since 5.558691·log v < Z there.
   - For v ≳ 5.80·10⁶ the top band 11.691 is weaker than Bellotti's VK.
   - Always take the max with the published regions, as phi5 `eta_base` does.
3. **Edge 28.73.** It was certified from float(28.73) = 28.73 + 4.26·10⁻¹⁶, while the CSV and phi5 read the exact decimal 28.73. The uncovered sliver (28.73, 28.73 + 4.3·10⁻¹⁶] is covered by MTY, which is stronger than Z = 18.922 there. Harmless; COSMETIC.
4. **Joint validity.** The rows are proved jointly, by induction with windows: each cell's window reaches 2.77 in v upward and the next band downward. Lowering any Z₂, or splicing rows into another profile, requires re-certification. Using the file as is, row by row, is fine.
5. **Closed region.** The CSV claims σ ≥ 1 − log v/(Z v). phi5 assumes the weaker σ >, which is fine.
6. **Tier.** Own proof (thesis method, unrefereed), with refereed inputs only: HPY, Yang JMAA Thm 1.1, Bellotti JMAA (VK, top window only), MTY, Ford, Kadiri, Heath-Brown, Ramaré, Rosser, Platt–Trudgian. It inherits the v1 reliance on thesis-text steps R1–R7 (REPORT §8.1), which the v1 review checked.
7. **Sensitivity.** If any input constant changes (1.546, 0.618, Ford's c's, Rosser's R₀), re-certify. Real margins are ~2·10⁻⁴ relative, so a change of more than ~0.02% in the main term breaks bands.

## 5. Issues

| # | Severity | Issue | Location |
|---|---|---|---|
| 1 | COSMETIC | Reported `minrel` is that of the first passing line, not the best one. The "1.6·10⁻⁸ thinnest margin" is an artefact; the true margin there is 1.8·10⁻⁴ | `cert_profile.cell_ok` (returns on first success); REPORT §11.2, §5.1 |
| 2 | COSMETIC | Wide v-balls at large v make `E_bound` return `nan`. This is safe, but causes 32–128× bisection (most of the 7.6 h run time) | `zl_core.E_bound`, `T = logT.exp()` |
| 3 | COSMETIC | Edge 28.73 is certified from float(28.73) > 28.73. The sliver is covered by MTY | `cert_v2.V0`, CSV row 1 |
| 4 | COSMETIC | Bands below v ≈ 30.07 and the upper part of the top band are weaker than published regions (no use, but true) | CSV rows 1–3, row 366 |
| 5 | COSMETIC | REPORT §11.3 could quote Yang Thm 1.1's uniformity statement (§5, l. 3247) and note that the CSV uses n ≤ 14 only | REPORT §11.3 |

## Files

| File | Purpose |
|---|---|
| `indep_v2.py` | Independent implementation. Modes: `cells` (iv cell checks vs `cell_terms`; extra cells via env `EXTRA_CELLS`), `scan` (dense point scan), `asym` (local requirement up to log t = 10²⁰). Outputs `cells_output.txt`, `scan_output.txt`, `asym_output.txt` |
| `rerun_v2.py` | Re-runs selected bands with the current code and records the argmin cell. Outputs `rerun_347_output.txt`, `rerun_misc_output.txt` |
| `ford_large_r.py` | Ford's W₀ bound at r up to 3·10⁶ via the exact series. Output `ford_large_r_output.txt` |
| `window_check.py` | Code window vs exact window. Output `window_check_output.txt` |
| `ball_cover.py` | v-ball covers the closed cell. Output `ball_cover_output.txt` |
| `probe_cells.py` | Shows the `nan` mechanism for wide cells (exploration) |
| `misc_numbers.py` | VK crossover of the top band (5.797·10⁶), MTY crossover (30.069), minimum µ_low. Output `misc_numbers_output.txt` |
