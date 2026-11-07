# Audit of RZA Lemma 3.1 (`m1e`)

*Sub-audit for `work/audit_rza/`. The subagent could not write report files, so the main session saved this report from its final message, with light formatting. The scripts and `*_out.txt` files in this folder are the subagent's.*

**Bottom line.** Nothing changes the constants 0.03, 4.1, (5+ε2^ε)/2 or the sign table of Lemma 3.1. Two side findings matter elsewhere:
- one constant in the proof of Lemma 6.2 (`A_est`) is wrongly justified (it can be repaired);
- display (`exxp`) in §6 is false as written.

**Sources.**
- RZ23 is arXiv:2312.05138v3 (12 Jan 2026). Its LaTeX is in `dl\v3\BV-Mobius-IdentityFactory-18.tex`; nothing from `dl\` was executed.
- RZ23 Thm 1.7 is `mqeps` (lines 353–424), proved in two parts (lines 1546–1623 and 1734–1897).
- RZ23 Lemma 5.2 is `basemq` (lines 822–842). Lemma 5.4 is `boundmqdex`, and the Thm 1.4 it relies on is `mqdex`.

**Notation.** D_q(X,ε) := Δ_q(X,ε)/X^ε, P_q(ε) := q^{1+ε}/φ_{1+ε}(q), F_1(x) := Σ_{n≤x,(n,q)=1} μ(n)log(x/n)/n.

## Verdicts

| # | Claim | Verdict |
|---|---|---|
| 1 | \|Δ\| bound with 0.03, 4.1, (5+ε2^ε)/2, the 2^ε factor and 1_{X≥10¹²}, for ε = σ−1 ∈ [0,1] | **VERIFIED** |
| 2 | m_q(X)/X^ε ≤ m_q(X;1+ε) | **VERIFIED, conditional on F_1 ≥ 0** (cited: Ramaré, Math. Comp. 84 (2015), Cor. 1.10; not re-proved in general) |
| 3 | the two lower bounds on Δ/X^ε | **VERIFIED** |
| 4a | ≤ 0 for X < 10.9, ε ≤ 4/25, all q | **VERIFIED (Arb)**, very tight margin |
| 4b | ≤ 0 for X < 47, non-exceptional classes | **VERIFIED (Arb)** for all ε ∈ [0,1] |
| 4c | ≤ 0.014 for X ≤ 47, class 1 | **VERIFIED**; 0.0031 is also certified |
| 4d | ≤ 0.00005 for classes 11, 13, 17 | **VERIFIED in a stronger form: Δ ≤ 0** |
| 5 | m-claims in the proof of `A_est` | four verified; **the max over the exceptional classes FAILS as stated** (repairable, see §4) |

## 1. The |Δ| bound

**What RZ23 does.** It never touches the tail −ε∫_X^∞ m_q t^{−1−ε}dt. Its "Identity Factory" (with g(n) = (−1)^{n+1}/n and H(t) = t^ε) turns the error into roughly ε/log 2 times the average X^{−1}∫_1^X|m_q|. The factor ε cancels the 1/ε in Δ, so the log X part stays bounded as ε → 0. A pointwise |m_q| bound on the tail would blow up.

We re-derived Thm 1.4 for real s = 1+ε from scratch and got the same intermediate bound as RZ23 lines 1578–1589:

|Δ| ≤ (2^ε/log 2)·X^{−1}∫_1^X|m_q| + (1 + 2^{1/2+ε}(1 + ε2^{ε−1}log 2))·√q/(φ_{1/2}(q)√X).

**Feeding in RZA Lemma 2.5.** This gives ∫_1^X|m_q| ≤ 1.03·H1·g_2·(…)·X/log X·1_{X≥10¹²} + g_0·(…)·√(8X). That needs T(y) = (log y/y)∫_{10¹²}^y dt/log t ≤ 1.03 for y ≥ 10¹², which we proved rigorously in Arb (the true maximum is 1.0295419, at y ≈ 1.3654·10¹⁵). The constants then check out in Arb:

| Constant | Check |
|---|---|
| 0.03 | 0.010333·2^ε/log 2 ≤ 0.02981 for ε ≤ 1 (holds up to ε ≈ 1.009) |
| 4.1 | √8/log 2 = 4.0806 |
| (5+ε2^ε)/2 | 1+√2 = 2.414 ≤ 2.42 and √2·log 2/2 = 0.490 ≤ 0.50 |
| 2^ε factor | follows from 1 ≤ 2^ε |
| 1_{X≥10¹²} | Lemma 2.5 has no log term for X < 10¹² |

**The g₁ → g₂ replacement is a real correction.** RZ23's Lemma 5.2 compares the wrong quantities: what is needed is 0.010032 × 1.4378 = 0.01442 ≥ 0.0296, which fails. So RZ23 Lemma 5.2, and with it Thm 1.7, is unjustified for even q when X ≥ 10¹². RZA's g₂ fixes this: 0.010032 × 2.9506 = 0.02960042 ≥ 0.0296.

The phrase "σ ∈ [1,2]" means ε = σ−1 ∈ [0,1].

## 2. Positivity and lower bounds

**Reduction.** X^ε m_q(X;1+ε) − m_q(X) = εF_1(X) + ε²∫_1^X F_1(t)(X/t)^ε dt/t. So claim 2 reduces to F_1 ≥ 0. The k ≥ 2 positivity that RZ23 also invokes follows from F_1 ≥ 0 as well.

**Source of F_1 ≥ 0.** RZ23 Lemma 4.1, i.e. Ramaré, Math. Comp. 84 (2015), Cor. 1.10. We did not obtain that paper.

**Our checks.**
- Rigorous (Arb): x ≤ 47, all q.
- Floats only: q ∈ {1,2,3,6,30,210}, x ≤ 10⁷.

**Lower bounds.** These follow at once: Δ/X^ε ≥ −P_q(ε)/(εζ(1+ε)) ≥ −q/φ(q), using εζ(1+ε) > 1.

## 3. Sign table (Arb, 192-bit, `sign_table_arb.py`)

**Method.** For each N = [X] and each worst-case q, the sup over X ∈ [N, N+1) is attained at an endpoint chosen by the exact sign of m_q(N). The script then bisects ε-cells, using rigorous enclosures of the ε-derivative. No cell failed.

| Claim | Cases | ε range | True max (approx.) |
|---|---|---|---|
| 4a | 91 | [0, 4/25] | −3.39·10⁻⁶ at q = 1, X → 10.9⁻, ε = 4/25 |
| 4b | 117,387 | [0, 1/10] | −0.0078 |
| 4b | 117,387 | [1/10, 1] | −1.5·10⁻⁴ (q = 19, X → 47⁻, ε = 1) |
| 4c | 47 | [0, 1] | 0.0030213, at X ∈ [29,31), ε → 0 |
| 4d | 138 | [0, 1] | −8.4·10⁻⁵ |

**How tight 4a is.** D_1(10.9⁻, ε) crosses zero at ε* ≈ 0.16849, so 4/25 cannot be raised much. At ε = 1/10 the value is −3.25·10⁻⁵.

**Possible sharpenings.** 0.014 → 0.0031 and 0.00005 → 0. RZA §6 only uses 4a, 4b and the lower bounds.

## 4. Claims in the proof of `A_est` (exact rationals; also `../rza_mpatterns.py`)

**Verified:**
- m ≥ 0 for t < 5 (the minimum is 1/6);
- Δ ≤ 0 for t < 5 and ε ≤ 1/10 (from 4a);
- m ≥ −1/30 on [5, 10.9) (attained);
- min ≥ −2323/30030 = m(13) on the non-exceptional classes (attained).

**FAILS:** "max m_ℓ(t) ≤ 57731/570570 on the classes {1,11,13,17}".
- The true maximum is m_11(15) = 69/455 ≈ 0.1516, and also m_13(15) = 53/385 ≈ 0.1377.
- 57731/570570 = m_17(22) is the maximum for class 17 only.

**Is a two-sided |m| bound needed?** Yes in principle, because Δ can take either sign in these classes. The minimum over the four classes is −2323/30030, so the lower side is fine.

**Repair.** The downstream constant survives. Using 4d in its stronger form (Δ ≤ 0 for classes 11, 13, 17) and |m_1| ≤ 19/210 on [10.9, 47), one gets m_ℓΔ_ℓ ≤ (19/210)|Δ_ℓ| ≤ (57731/570570)|Δ_ℓ|. So ax₂ = 0.1012 is valid with this repaired argument. With only what the paper states, ax₂ would have to be 69/455.

**Typos.**
- Line 1554: "ℓ < X/47" should read "ℓ > X/47".
- Line 1586: the factor √ℓ/φ_{1/2}(ℓ) is missing on the 4.1·g₀ term. The later definition of A₁ has it, so this is cosmetic.

## 5. Numerical sanity check (floats, not a proof)

The test covers q ∈ {1,2,3,6,30}, ε ∈ {10⁻⁴, 0.01, 0.04, 0.1} and all X ≤ 10⁷.
- |Δ| is at most 0.214 of the Lemma 3.1 bound (worst at X ∈ [1,2)), and at most 0.008 of it for X ≥ 10⁵.
- The intermediate bound of §1 holds with ratio ≤ 0.414.

## 6. Side findings outside Lemma 3.1

**Display (exxp) is false.** RZA display (exxp) (lines 1478–1489) is false as written; see `../REPORT.md` §3. The Arb check `check_exxp.py` gives:

| X | ε | S_ε(X) | RHS |
|---|---|---|---|
| 100 | 1/10 | 0.3768 | 0.2952 |
| 1000 | 1/10 | 0.3110 | 0.2258 |

## Not checked

- RZA Lemma 2.5's own inputs (Helfgott's bounds); only its g₂ arithmetic was checked.
- The general case of F_1 ≥ 0.
- RZ23's derivative lemma for Δ (`derDelta`) and its Pari algorithm. Our sign-table proof does not use them.

## How to re-run

Requires Python 3.12, python-flint 0.9.0, numpy, scipy and mpmath. Run each script as `python -I <script> > <script>_out.txt`.

| Script | What it checks | Time |
|---|---|---|
| `check_constants.py` | Part 1 constants, T(y) ≤ 1.03 | ~2 s |
| `check_m_values.py` | exact m-values, F_1 ≥ 0 for x ≤ 47 | ~12 s |
| `sign_table_arb.py a,c,c_tight,d0` | claims 4a, 4c, 4d (→ `sign_table_acd_out.txt`) | ~5 s |
| `sign_table_arb.py b1,b2` | claim 4b (→ `sign_table_b_out.txt`) | ~8 min on 15 processes |
| `explore_sign.py` | float exploration of the sign table | — |
| `check_delta_bound.py` | float check of the \|Δ\| bound | ~1 min |
| `check_F1_float.py` | float check of F_1 ≥ 0 up to 10⁷ | — |
| `check_exxp.py` | Arb check of (exxp) | ~3 s |

`crossing_10p9_out.txt` comes from an inline mpmath one-liner (the root of D_1(10.9⁻, ε)).
