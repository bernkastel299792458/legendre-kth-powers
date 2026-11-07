# Phase 0 — Bellotti's log-free zero-density table: audit, repair, re-optimisation

*Written by the Phase 0 sub-agent and saved by the main session; the sub-agent could not write report files. All code and CSVs in this folder are the sub-agent's. Every CSV row passes `verify_rows.py` in pure Arb.*

## 1. Verdict: the counting gap in §4 is real

Citations are to arXiv v2: `work/ref/bel_v2.txt`, which agrees with `proof/input_verification/sources_density/2405.12545v2.txt`. The published JNT version was **not** checked (UNSURE whether it differs).

**What the paper says.**
- Before (4.9): "for every fixed γ_r there is a unique representative zero … with |γ_r−γ_s| < δ".
- Before (4.11) and (4.13): "for each n … a unique representative zero … with nδ ≤ |γ_r−γ_s| ≤ (n+1)δ".
- Representatives are chosen arbitrarily in boxes of height δ (4.1).

**Why the claim is false.** Take γ_r in box m. A representative in box m+k lies at distance greater than (k−θ)δ, where θ is the position of γ_r within its box.
- Up to 3 representatives can satisfy |γ_r−γ_s| < δ: r itself and its two neighbours. Example distances: 0.99δ and 1.01δ.
- A band of width δ can contain up to 2 representatives on each side, so 4 in total.
- Adversarial configurations give a per-representative sum of 10.99, against her claimed 5.99 (`counting_check.py`).

**The factor 2 in (4.6)/(4.7) does not cover both sides.** It comes from |X^z − (U/L²)^z| ≤ 2X^{Re z}. It is already used up in (4.9), where 2·1/(2δ) = 1/δ.

**Minimal fix.** c₂' = 3K·c₂, c₃' = 2c₃, c₄' = c₄. Her unexplained 2.4 happens to cover both sides of c₄, because 2δS(1) + 2∫S ≤ 2.4∫S. The overall factor is about 1.97.

**Sharp fix (used everywhere).** Pair the representative at offset +j with the one at −j:
- Hn = g[K/2 + Σ_{j≤J₁} P_j] + 2δ·S(1) + (2/λ)∫₁^∞ S, with J₁ = ⌈1/(λν(T))⌉.
- P_j = m(j−1) + m(j) in the convex region, otherwise m(j−1) + m(j−½), where m(d) = min(K/2, 1/(λd)).
- A = 2·d₄d₅·Hn/w replaces c₂+c₃+c₄.
- The bound is within 0.03–2% of the exact worst case.

The relation N ≤ J·ñ is unchanged and correct.

## 2. Other problems found

The sub-agent's inferences. Each is fixed in `belarb.py`.

**(a) d₃ code slip, confirmed.** Her code's d₃ is too small by a factor log²T compared with the paper's (3.6). Effect: +1.0–1.6% on C.

**Lemma 3.2.** The proof is flawed: the (2,2) term needs log V and V² < N, not log U and UV < N. The fix replaces d₄ by a bound from RZA Cor. 1.2 alone, d₄ ≤ T^{u−x} + 3.09·F(v/u)·x/(v−u). Effect: +5–7.5%.

**(b) Monotonicity in (4.9).** The step "X^{2−y}/(2−y) decreasing" needs x > Z(T)/2. This fails on her Ford rows from e^100 up, and above e^170.2. A factor K = e^{κ−1}/κ ≤ 1.018 covers it. Effect: ≤ 0.3% up to e^170.2.

**|G(½+it)| ≤ W·|G(1)| (after (4.14)) is invalid.** G(1) relies on cancellation, and the absolute values lose it. Proved replacement: |G(½+it)| ≤ 16·P_h·W/log²W with P_h ≤ 1.48111. Effect: c₅ ×1.5–2.4, which is +4–17% on C.

**(3.10).** It has (u+w)⁴ where (v+w)⁴ is needed, in both the paper and the code.
- Effect: +14% on row 1, and ≤ 0.3% beyond e^33.
- It matters only because she uses γ > 0.447 log T. With γ > 3·10¹² (Platt–Trudgian) it is negligible.

**Lemma 2.7.** The proof uses d₁(X) for every u ≤ X, but d₁ is decreasing. Her code also evaluates d₂,₁ with permuted arguments. Replaced by a rigorous bound, about +3% on that quantity.

**Harmless points.**
- (3.20) claims Ψ(n) = Λ(n)/log(V/U) for n > U, which is false, but the term is negligible.
- Stirling is used with Re z < 0. It is justified through Γ(z) = Γ(z+1)/z.
- Lemma 2.2 has 4.7098 and Cor 2.3 has 4.7908; the latter is conservative.
- Her b₁ omits a √2 but is still valid.
- Her Γ constants 1.808, 3.62642 and 4.05206 are exact at the extreme σ'.
- Patel–Yang's 66.7·t^{27/164} holds for t ≥ 3, so using it below e^105 is legitimate.

**Two rows were computed with α₀ 0.0001 lower than printed.** (e^50, e^60] used 0.9891 and (e^60, e^70] used 0.9875, so the printed rows are conservative.

**Ford region (2.2).** This is Yang JMAA 2024 eq. (1.4). It is used only for T ≥ e^33; below 1.88·10¹⁴ the MTY region 5.558691 covers (checked in Arb).

## 3. Arb implementation and validation

**Implementation.**
- `belarb.py` has two parts:
  - a literal Arb transcription of her code (`faithful`);
  - a generic corrected bound, with one switch per correction.
- The corrected bound takes a rigorous supremum over the whole row by adaptive bisection.
- Every lemma hypothesis is checked in Arb over the row (`check_hypotheses`).

**Validation, with corrections off and her parameters.**
- 29 of 35 rows match her printed C to ≤ 1.9·10⁻⁷.
- The two α₀-shifted rows match to 10⁻⁸ once α₀ is set to the value she actually used.
- Above e^170.2 the printed C is our value rounded up to 3 significant figures; the maximum raw discrepancy is 8.3·10⁻³.
- `belmodel.py` agrees with the Arb code to ≤ 2·10⁻¹⁵.

## 4. Corrected faithful table (`rows_corrected_faithful.csv`)

**Setup.** Her parameters, her zero-free regions and γ > 0.447 log T, with all corrections on.

**Checks.** All hypotheses pass on every row with log T₁ ≤ 3000. The two widest rows were evaluated at T₀ only and are marked UNSURE.

| Her row (log T) | C printed | C corrected | Ratio |
|---|---|---|---|
| 28.73–29 | 37341.72 | 82004.4 | 2.196 (1.892 with γ > 3·10¹²) |
| 31–46.2 (15 rows) | | | 1.94–2.00 |
| 46.2–50 | 104761 | 207789 | 1.984 |
| 60–70 | 194324 | 398372 | 2.050 |
| 70–80 | 278045 | 586967 | 2.111 |
| 80–90 | 370656 | 800577 | 2.160 |
| 90–100 | 425721 | 910526 | 2.139 |
| 100–110 | 488901 | 1041080 | 2.129 |
| 160–170.2 | 909966 | 1873940 | 2.059 |

The full per-row, per-correction breakdown is in `corrected_factors.txt`.

**With her parameters the printed C is too small by about 2.0–2.2×. The v4 results (k ≥ 70 tolerates C×1.1; k ≥ 74 tolerates C×1.05) are therefore not supported as they stand.**

## 5. Re-optimised frontier (`rows_reopt.csv`, `rows_reopt_lam1.csv`)

**Small improvements.**
- The factor 2 in (4.6) becomes 1 + (Y/X)^{2ν(T)}, since Re z ≥ 2ν(T).
- g = 1, since Γ(1+s) ≤ 1.
- Exact b₁ and b₂.
- γ > 3·10¹² (Platt–Trudgian).

**Major modification: boxes of height λδ instead of δ.** Bellotti's case is λ = 1.
- Each box lies in a disc of radius δ√(1+λ²/4) < ½, as Prop 2.11 requires.
- The pair-sum accounting above holds for any λ, and the sampled worst cases stay within it.
- The optimum is λ ≈ 10–13.

**Tier caveat.** Bellotti's published proof is flawed, so every corrected row, including λ = 1, is strictly "refereed inputs + our own repair or modification". The CSV status column records only the tier of the *inputs*: "refereed", or "audited preprint" if the BTY 4.896 region is used.

**Intervals and options.**
- Interval widths: 1 from log(3·10¹²) to 80, 2 up to 110, and 4 up to 170.2, plus six wider rows up to 500.
- Options per interval:
  - B ∈ {B_her, B_her ± 1, B_her + 2, B_edge}, where B_edge minimises C·e^{B/Z};
  - α₀ ∈ {hers, 0.985, 0.98}, with 0.98 only for log T₁ ≤ 110;
  - both zero-free region sets.
- **Why B_edge.** Unconstrained minimisation of C is useless, because C keeps falling as B grows.
- **Output.** 1596 rows with optimised λ, and 266 rows with λ = 1.
- **Infeasible options.** B_her − 1 near the bottom of her wide rows (114 cases); these are absent from the frontier.

**C_new / C_printed at the same B,** refereed region set (BTY set in brackets):

| Height | Interval just below (λ* / λ=1) | Interval just above (λ* / λ=1) |
|---|---|---|
| e^29 | 0.200 [0.173] / 1.049 [0.882] | 0.199 [0.173] / 1.048 [0.881] |
| e^50 | 0.212 [0.187] / 1.073 | 0.252 [0.224] / 1.254 |
| e^70 | 0.190 [0.187] / 0.910 | 0.298 [0.294] / 1.374 |
| e^80 | 0.209 / 0.966 | 0.312 / 1.411 |
| e^90 | 0.231 / 1.045 | 0.314 / 1.422 |
| e^100 | 0.240 / 1.088 | 0.317 / 1.436 |
| e^110 | 0.248 / 1.126 | 0.318 / 1.442 |

**Low heights.** α₀ = 0.98 rows now exist at e^29–e^40. For example, [28.73, 29] with B = 14.16 has C = 13133 (refereed).

## 6. verify_rows.py

For every row the script:
- rebuilds the parameters;
- rechecks every lemma hypothesis over the row;
- recomputes the rigorous supremum of C;
- asserts C_claimed ≥ that bound and B ≥ 2x;
- checks that the status matches the inputs.

| CSV | ok | skipped (UNSURE) | failed |
|---|---|---|---|
| rows_corrected_faithful.csv | 37 | 2 | 0 |
| rows_reopt.csv | 1596 | 0 | 0 |
| rows_reopt_lam1.csv | 266 | 0 | 0 |

## 7. Conventions

- Each row asserts N(σ,T) ≤ C·T^{B(1−σ)} for every T with logT0 < log T ≤ logT1 and every σ ∈ [α₀, 1].
- **Counting.** Our corrected proof counts N(σ,T) = #{ρ : β ≥ σ, 0 < γ ≤ T}; nothing uses strictness. Bellotti states σ < β < 1, 0 < γ < T.
- **Lowest rows.** Rows with logT0 = 28.7296 are computed from log(3·10¹²); below that, N = 0.
- **Notes column.** It records the box height λ and the option set (`lam=…; opt=IMPR`).

## 8. Open doubts (UNSURE)

- Whether the JNT published version differs from arXiv v2.
- What her factor 2.4 in (4.13) was meant to cover (no longer used).
- The supremum over T for the rows (e^3000, e^481958] and for the Korobov–Vinogradov range was not verified.
- The validity range of the Ford region (2.2) according to Yang and MTY; it is used only for T ≥ e^33, with a fallback.
- RZA Cor. 1.2 was taken from arXiv v1, not from the Funct. Approx. version.
- The Stirling bound for 0 < Re z ≤ 3/4 rests on Olver plus the sub-agent's own Taylor argument.
- **The counting repair, the λ-box modification and the small improvements are new arguments. They need independent review before any claim relies on them.**

## 9. How to re-run

- `python reproduce_table2.py` (about 5 s).
- `python corrected_table.py` (about 15 s).
- `python frontier.py shard k 12` for k = 0..11, then `python frontier.py merge 12` (about 6 min in parallel).
- `python summarize_frontier.py`.
- `python verify_rows.py [--shard=k/n]`.

## 10. Addendum (milestones 6–8): high rows, Phase 2 lemmas, fixes

*Saved by the main session from the sub-agent's final message.*

### 10.1 Files

| File | Rows | Note |
|---|---|---|
| rows_high.csv | 200 | |
| rows_high_v2.csv | 160 | |
| rows_reopt_v2.csv | 1345 | |
| rows_corrected_faithful.csv | 39 | all certified now |

Code:
- `belarb.py`: new `piece_hl`, `piece_v2`, `Hn_general`, `OPT_IMPR_H`, `OPT_CORR_H`, `OPT_V2`.
- `high.py`, `v2.py`, `summarize_v2.py`.
- `verify_rows.py` now covers every CSV. Every row passes; nothing fails.

### 10.2 High rows: rows_high.csv

**Coverage.** log T ∈ (500, 2·10^6], in 40 intervals, all with α₀ = 0.985.
- On (500, 3000] the intervals follow Bellotti's edges.
- Above 3000 they are geometric, with ratio about 1.25.

**Five rows per interval.**
- `CORRH`: her parameters, with her zero-free regions (Littlewood 21.233; KV 53.989 above 481958).
- `IMPRH` with λ* ≈ 10–11, at B = B_her and at B = B_edge.
- `IMPRH` with λ = 1, at B = B_her and at B = B_edge.
- The IMPRH rows use Littlewood 21.233 and KV 54.004.

**Rigorous sup over T.** `piece_hl` evaluates the same bound in a rearranged form, so that it stays stable on wide L-ranges:
- products of exponentials are replaced by the net exponent;
- d₅ is written as 1 + c/(wL);
- ν·log T is computed directly.

It agrees with the ordinary evaluation to 0.07%. The sup uses adaptive bisection, and every sub-range contributes an upper bound.

**Previously UNSURE rows, now certified.**
- BELCORR38 (3000, 481958]: C = 7.56192·10^8, 1.313× the printed value.
- BELCORR39 (481958, 6.7·10^12]: C = 1.73058·10^11, 1.068× the printed value.

**C/C_printed at B = B_her.**

| log T | her parameters | λ* | λ = 1 |
|---|---|---|---|
| 500–3000 | 1.34–2.00 | 0.12–0.33 | 0.52–1.46 |
| 3000–481958 | 1.31 → 0.89 | 0.019–0.21 | 0.085–0.95 |
| > 481958 | 0.77–1.01 | about 0.002 | 0.006–0.009 |

With B_edge (B ≈ 3.4–7.1), C ≈ 7·10³–2·10⁴ for λ*, and C ≈ 3·10⁴–8·10⁴ for λ = 1.

### 10.3 Phase 2 lemmas: rows_reopt_v2.csv and rows_high_v2.csv

**How each lemma enters.**
- **Lemma A.** `d4_upper` is evaluated once per row, with ε = 2.05/(x·log T_mid). It replaces d₄ in the pair sum and in c₅.
- **Lemma B.** `cf_upper(hfac = λ)` replaces b₁ + b₂Z.
- **Lemma C.** It is built into the pair accounting:
  - every pair satisfies ≤ (X^{2δ} − Y^{2δ})/(2δ);
  - a pair at distance D also satisfies ≤ (1+ε_Y)X^{2δ}/D, where ε_Y = (Y/X)^{2ν(T)};
  - per pair, take min((1−q)/2, (1+ε_Y)/(λd)), with q = (Y/X)^{2(1−α₀)};
  - the far part uses Stirling with the same factor (1+ε_Y).

  No monotonicity of X^y/y is needed, so the factor K disappears. With Lemma C switched off, the old bound is reproduced exactly (7460.156).

**Optimisation and certification.** u, x, v, w are optimised per interval with λ ∈ {1, 8, 14, 18, 22}, using `d4_model` and the rigorous cf. Each row is then certified with the rigorous d4_upper, the Arb bound and all hypothesis checks. In practice λ ends up at 14–22.

**Row tags.**
- Each row records `lems=lemA,lemB,lemC`, `lemB,lemC` or `lemC`.
- It also stores d4A, epsA and cfB, plus cfLsteps for the high rows.

**rows_reopt_v2.csv: 1345 rows, log T ∈ [28.73, 500].**
- By lemma set: 803 rows use A+B+C, 271 use B+C, 271 use C only.
- By status: 865 refereed, 480 audited preprint. The 4.896 region matters only below log T = 73.
- B options: B_edge, B_her, and 0.85 / 0.72 / 0.62 × B_her where feasible. The 106 infeasible cases are omitted.
- α₀: her value, plus 0.98 (for B_her and B_edge).
- Lemma A is not used on (200, 500], because its block count grows with log T.

**C at B_her, all lemmas, refereed region set** (×printed in brackets):

| height | interval below | interval above |
|---|---|---|
| e^29 | 185 (0.0050) | 192 (0.0051) |
| e^50 | 414 (0.0040) | 539 (0.0042) |
| e^70 | 600 (0.0031) | 1017 (0.0037) |
| e^80 | 818 (0.0029) | 1279 (0.0035) |
| e^90 | 1065 (0.0029) | 1438 (0.0034) |
| e^100 | 1222 (0.0029) | 1614 (0.0033) |
| e^110 | 1394 (0.0029) | 1775 (0.0033) |
| e^166–e^170.2 | 2513 (0.0028) | |

**Other options.**
- B_edge (B ≈ 8.3–14.3): C ≈ 160–190 up to e^200.
- Lowest feasible B, for example:

  | height | B | C |
  |---|---|---|
  | e^29 | 8.78 | 1030 |
  | e^70 | 4.80 | 2730 |
  | e^110 | 3.84 | 3420 |

- Lemmas B+C only: 0.09–0.14 × printed. Lemma C only: 0.16–0.26 × printed.

**rows_high_v2.csv: 160 rows, log T ∈ (500, 2·10^6].**
- Lemmas B+C, or C only, with 12 geometric pieces per row for Lemma B.
- At B_her with B+C, C/C_printed is:

  | log T | C/C_printed |
  |---|---|
  | 500–3000 | 0.05–0.14 |
  | 3000–481958 | 0.01–0.09 |
  | above 481958 | about 0.001 |

- B_edge gives C ≈ 4·10³–1.5·10⁴.
- 0.85 × B_her is mostly infeasible on (e^3000, e^481958].

### 10.4 Fixes and process notes

**Edge fix (review §3.4).** Count only zeros with 3·10^12 < γ ≤ T. Replace each box by the sub-box [max(t₀, 3e12), min(t₀ + λδ, T)].
- The sub-box is no taller than the box.
- Its centre lies in [3e12, T].
- It fits in the disc of radius ρδ about its own centre.

Shifting a box that straddles 3e12 is legitimate, because RH has been verified up to 3e12. No number changes.

**Points raised in the Phase 2 review.**
- `residue_factors` and `b1b2_upper` are not called, so neither the f₂ branch nor the sampled λ_min affects any row.
- For rows with the Ford region, `check_hypotheses` certifies that the Ford width decreases on [32.8, log T₁] (sign of the derivative) for rows up to e^500.
- The tag for TZ's input should be Hiary 2016 (0.63), not HPY 0.618.

**Joint sup over δ.** Rows with Lemma B already take the joint sup, because cf is a sup over δ. Rows without Lemma B keep separate sups.

**Precision bug, fixed.** The Phase 2 modules set ctx.prec = 100 on import. As a result, the verifier's bound could exceed the claimed value by up to the adaptive tolerance of 10⁻³.
- v2 claims now carry 0.25% headroom, and d4A and cfB are rounded up by 10⁻⁶.
- The verifier pins precision at 128 bits.
- rows_high_v2 was regenerated and re-verified.
- The older CSVs were re-checked: in full for faithful and high, by sample for reopt and lam1. All pass.

**Bug in a v2 run, fixed.** The high-L hypothesis shortcut assumed the Ford region was absent. It now uses a subdivided check, and the run was repeated.

**Tiers.** The CSV status column records only the status of the inputs. All corrected and re-optimised rows also rely on our own repair of §4 and on the λ-box lemma (both confirmed by review). The v2 rows additionally rely on Lemmas A/B/C as tagged (confirmed by review).

**Re-run.**
- `python high.py shard k 12` for k = 0..11, then `python high.py write 12`.
- `python v2.py shard k 12` for k = 0..11, then `python v2.py shard_mid k 4` for k = 0..3, then `python v2.py write 12`.
- `python v2.py shard_high k 4` for k = 0..3, then `python v2.py write_high 4`.
- `python verify_rows.py [file] [--shard=k/n]`.

**UNSURE.**
- The exact validity statement of the Ford/Yang region.
- The RZA journal text (we used v3).
- Lemma A was not run above e^200.

## 11. Addendum, milestone 9: low-height rows (rows_low_v3.csv, final; recorded by the main session)

**Coverage.** 2534 rows on log T ∈ [28.73, 110]. Every row passes `verify_rows.py` in Arb with 0 failures. Chourasiya–Simonič is not used anywhere.

**Zero-free region (`cl_local`).** The input is phase1_littlewood Theorem C, from `zfr_classical_local.csv`: our own proof by the BTY method, using refereed inputs only.
- ν(T) is the minimum over all bands meeting (log 3e12, log T] of 1/(Z_j·min(b_j, log T)). This is a running minimum, so the bands need not be monotone.
- Band edges are compared as exact arb values. A band is skipped only if its lower edge is certainly above log T.
- Above log T = 59.5 the rows use MTY, Ford and Littlewood instead.

**Grid.** Interval widths are 0.1 up to log T = 30, 0.25 up to 33, 0.5 up to 40, 1 up to 59 (previous set) or 80 (new set), and 2 up to 110.

**Merit.** log C + B/Z1(T0) + log(1600/(1600 − B·log T0)). Each row records Z1loc and its merit in the notes.

**Rows by lemma set.**

| Lemma set | Rows | Range | α₀ | B |
|---|---|---|---|---|
| A, B, C | 1044 | [28.73, 59] | 0.99–0.96 | B*, 0.85·B*, 0.7·B* |
| B, C | 116 | [28.73, 59] | 0.985, 0.98 | — |
| C only (half with count=joint) | 232 | [28.73, 59] | 0.985, 0.98 | — |
| A, BW, C, D, with `c1zeta=hpy` | 1142 | 521 on the seam, 621 on [33, 110] | — | — |

α₀ may go down to 0.95, subject to α₀ < 1 − ν(T₀).

**Results.** The seam gains about e^{1.35}, i.e. ×3.9 in C·e^{B/Z1}. The best rows (α₀ = 0.99):

| Interval | B | C | merit | earlier best |
|---|---|---|---|---|
| [log 3e12, 28.8] | 9.23 | 139.1 | 7.118 | merit 8.486 |
| [32.75, 33] | 8.91 | 146.6 | 7.100 | merit 8.346 |

Above 33, C·e^{B/Z} compared with v2:

| Height | ratio to v2 |
|---|---|
| e^33 | ×0.30 |
| e^40 | ×0.33 |
| e^50 | ×0.38 |
| e^60 | ×0.48 |
| e^70 | ×0.50 |
| e^80 | ×0.52 |
| e^90 | ×0.54 |
| e^100 | ×0.56 |
| e^110 | ×0.58 |

**How the new lemmas enter (`belarb.piece_v2`).**
- **Lemma D.** K_D replaces D2VW in c₁'s SU, E312 and E313; S1t keeps D2VW.
- **Lemma B-W.** Uses `cf_upper(weyl=True)`. A_η is replaced at run time by an arb upper bound (`patch_phase2_rounding`), and the verifier uses the patched value.
- **HPY in c₁.** The main term takes min(66.7·t^{27/164}, 0.618·t^{1/6}·log t), with I2coef_hpy = 1.2787.
- **Lemma D with U = 1 in c₅.** Not applied; c₅ is negligible with Lemma A.
- **Precision** is pinned at 128 bits after the Phase 2 imports.

**Joint sup over δ (`count=joint`).** Rigorous by construction. It gains only 1–3.5% on these rows.

**Fixes made during verification.**
- **Band-edge rule.** The final rule matches how the rows were certified. Before it, 51 extension rows were off by at most 1.6e-4 in cf; all 692 affected or extension rows now re-verify.
- **v3.write merit region.** It now uses each row's own region.

**Re-run.**
1. `python v3.py shard k 14` (k = 0..13).
2. `python v3.py shard_b k 12 0 25` and `python v3.py shard_b k 12 25 94` (k = 0..11).
3. `python v3.py write 14`.
4. `python verify_rows.py rows_low_v3.csv`.

**UNSURE.**
- Rademacher's lemma is used as usually quoted.
- One TZ inequality is taken from inside their proof.
- All the new lemmas (A, B, BW, C, D, Theorem C, the λ-box, the §4 repair) are our own. They have been reviewed internally, but by no external referee.
- Lemma A's constants are taken from RZA arXiv v3.
- Ford/Yang's validity range is still open.

## 12. Addendum, round 4: rows_mid_v4.csv on log T ∈ [110, 600] (recorded by the main session)

**Contents.** 1251 rows. All pass `verify_rows.py` with 0 failures, and a content-based check confirms that every row comes from a verified run.

**Tags.** Every row carries `lems=lemA,lemBW,lemC,lemD`, `c1zeta=hpy`, zero-free region input `lw_local+lw21.233+kv54.004+ford` (Ford only for log T ≥ 33), and status `refereed`. Chourasiya–Simonič is not used.

**Grid.**
- Interval widths: 2 up to log T = 200, 5 up to 400, 10 up to 600.
- α₀ ∈ {0.99, 0.98, 0.97, 0.96}.
- B ∈ {B*, 0.85·B*, 0.7·B*}.
- Missing: the 9 rows with α₀ = 0.96 on [500, 530], where the optimisation was infeasible.

**Merit.** log C + B·ν(T₀)·log T₀ + log(38/(38 − B)).

**Headroom.** The claimed C is 0.25% above the computed bound. d4A and cfB are rounded up by a factor 1 + 10⁻⁶, and the computation runs at 128 bits.

**Results.** α₀ = 0.99 gives the best row in every interval. Against the earlier rows, C·T₀^{Bν} improves by about ×0.50 up to log T = 200 (where the earlier rows already used A+B+C) and by about ×0.024 above 200 (where they used B+C only). Examples:

| interval | B | C |
|---|---|---|
| [110, 112] | 6.92 | 145.8 |
| [200, 205] | 6.10 | 150.6 |
| [350, 355] | 5.54 | 159.1 |
| [590, 600] | 5.05 | 172.8 |

**Files.** `v4.py`, `v4_raw.json` (re-running reproduces the CSV byte for byte), `v4_summary.txt`, `idle_run.py`. The computation used at most 4 processes, at idle priority.
