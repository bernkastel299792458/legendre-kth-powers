# Phase 2: new lemmas that shrink Bellotti's constant C

*Workstream `work/phase2_lemmas/`. The report was written by the Phase 2 sub-agent; the sub-agent could not write report files, so the main session saved it.*

- Every number called a "bound" is an Arb (python-flint 0.9.0) upper bound.
- The assembly of C from the lemma outputs (§4) is a **float model** of Bellotti's formula. It estimates the effect; it is not a certified C.
- Re-run with `python verify_all.py` (about 3 minutes on 14 cores). Last run: **ALL OK**.

## 0. Verdicts

| Item | Replaces (Bellotti, arXiv:2405.12545v2) | Proof | Verification | Effect on C, her parameters |
|---|---|---|---|---|
| **Lemma A** | d₄ (Lemma 4.2, via RZA Cor 1.2 + (3.6)) | complete | Arb, `lemmaA_d4.py` | **×0.030–0.050** (d₄: 85–236 → 4.4–7.7) |
| **Lemma B** | b₁ + b₂Z (Lemma 2.4 / Cor 2.3 / TZ Prop 2.11) | complete; one input is an inequality proved inside TZ's proof | Arb, `lemmaB_count.py` | **×0.54–0.60** for her boxes; ×0.76–0.80 for Phase 0's boxes of height λδ, λ ≈ 10–13 |
| **Lemma C** | the factor 2 in (4.6) | complete, elementary | Arb, `lemmaC_residue.py` | **×0.57–0.78** |
| A+B+C | — | — | float assembly (`effect_on_C.py`) | **×0.012–0.017** |
| Item 4 (smoother weights) | — | not attempted | — | — |

**Input status.**
- Lemma C uses only refereed inputs.
- Lemma B uses Heath-Brown (1992) and Thorner–Zaman (Forum Math. 2024), both refereed.
- Lemma A uses Ramaré–Zuniga-Alterman's "identity factory" (Math. Comp. 2026, refereed).
  - The constants were read from arXiv v3; the journal text was not checked (UNSURE).
  - That paper relies on Helfgott's unrefereed computation |m(x)| ≤ √(2/x) for x ≤ 10¹².
  - The input enters only through a tiny error term (§1.5).

**All three lemmas are our own new lemmas. They need independent review before anything relies on them.** Lemma A in particular gains a factor of about 20.

**Why the size of Lemma A's gain is plausible.**
- The true d₄ is about 1.6–2.6. This comes from the model in §1.7 and agrees with `ref/bv.py`.
- RZA's bound, as Bellotti uses it, is 30–65× too large.
- Ours is about 2.7× the true value.

## 1. Lemma A: the harmonic L² sum of the Barban–Vehov weights (d₄)

**What d₄ bounds.** Notation:
- U = T^u, V = T^v, X = T^x, L = log T, Δ = (v−u)L;
- ψ_d = μ(d)g(d), with g(d) = (log⁺(V/d) − log⁺(U/d))/Δ;
- Ψ(n) = Σ_{d|n} ψ_d.

In (4.3) / Lemma 4.2, d₄ is any upper bound for

**S := Σ_{n≥1} Ψ(n)²n⁻¹(e^{−n/X} − e^{−nL²/U})**.

Bellotti splits the sum at UV and uses RZA Cor 1.2 for [U, UV] and (3.6) for the tail. Lemma A bounds the whole of S directly, so d₃ and (3.6) are no longer needed.

**Lemma A.** Let 0 < u < v, x > 0, T ≥ 3·10¹², and s = 1+ε with 0 < ε ≤ 1/10. Put
- M(y) = Σ_{m≤y} μ(m)m^{−s} log(y/m) for y ≥ 1, and M(y) = 0 for y < 1;
- H(n) = M(V/n) − M(U/n).

Then

(A1) Σ_{n≥1} Ψ(n)²n^{−s} ≤ (ζ(s)/Δ²) Σ_{n≤V} H(n)²n^{−s};

(A2) S ≤ L²/U + (εX/e)^ε (Σ_{n≥1} Ψ(n)²n^{−s} − 1).

**Proof of (A2) (Rankin).**
1. Ψ(n) = 0 for 2 ≤ n ≤ U, since g(d) = 1 for d ≤ U. Also Ψ(1) = 1.
2. The weight w(n) lies in (0, 1), and w(1) ≤ L²/U by the mean value theorem.
3. For n > U, w(n) ≤ (εX/e)^ε n^{−ε}, because max_y y^ε e^{−y} = (ε/e)^ε. ∎

A float LP over 40 exponents always picks a single exponential, so a sum of several gives nothing more.

**Proof of (A1) (new diagonal inequality).**
1. Σ_n Ψ(n)²n^{−s} = ζ(s)Q, where Q = Σ_{d,e} ψ_dψ_e[d,e]^{−s}.
2. Since [d,e]^{−s} = (de)^{−s}(d,e)^s and (d,e)^s = Σ_{δ|(d,e)} φ_s(δ) with φ_s = μ⋆N^s > 0, we get Q = Σ_δ φ_s(δ)y_δ², where y_δ = Σ_{δ|d} ψ_d d^{−s}.
3. For squarefree δ, y_δ = μ(δ)δ^{−s}F_δ, where F_δ = Σ_{(m,δ)=1} μ(m)m^{−s}g(δm).
4. Using μ(m)1_{(m,δ)=1} = Σ_{jk=m, k|δ^∞} μ(j), we get F_δ = Δ^{−1}Σ_{k|δ^∞} k^{−s}H(δk).
5. Cauchy–Schwarz with weights k^{−s}, together with Σ_{k|δ^∞} k^{−s} = δ^s/φ_s(δ), gives φ_s(δ)y_δ² ≤ Δ^{−2}Σ_{k|δ^∞}(δk)^{−s}H(δk)².
6. The map (δ, k) ↦ δk is a bijection onto the positive integers (δ = rad n). Hence Q ≤ Δ^{−2}Σ_n n^{−s}H(n)², and H(n) = 0 for n > V. ∎

**Remarks.**
- (A1) is sharp to first order.
- RZA lose because they use (a−b)² ≤ a²+b², which throws away the cancellation between M(V/δ) and M(U/δ).

**Analytic input (A3).**
- **Source.** RZA identity factory, arXiv:2312.05138v3, theorem `mcheckqeps` with q = 1.
- **Statement.** For σ = 1+ε ∈ [1, 11/10] and y ≥ 15,
  M(y) = A + B log y + R(y), with B = 1/ζ(σ), A = −ζ′(σ)/ζ(σ)², and
  |R(y)| ≤ 2^ε y^{−ε}[0.0336·1_{y≥10¹²}/log y + (7.79 + 2.83ε log y + 5.17ε)/√y].
- **How it is used.** We use a monotone majorant of this bound, and only for y ≥ 10⁶, where it is ≤ 0.0073.
  - The true |R| there is about 10⁻⁵.
  - Multiplying the bound by 10 raises d₄ by only 2.9%.
- **Below 10⁶.** For y ≤ 10⁶, M is tabulated exactly in Arb. Its piecewise form is M(y) = P_k log y − Q_k on [k, k+1).

**Rigorous evaluation (`lemmaA_d4.py`).**
- The range of log T is split into pieces of width ≤ 0.25.
- ε = a/(x·L_mid) with a ∈ {1.8, 2.05, 2.3}, keeping the best.
- **n ≤ 10⁵:** H = BΔ + R − R.
- **10⁵ < n ≤ U:** blocks in w = log(U/n), using the exact min/max of M from the table, or the majorant of R.
- **U < n ≤ V:** blocks in log(V/n).
- **Block sums** use Σ_{a<n≤b} f ≤ ∫_{a−1}^b f for decreasing f.
- **Monotone substitutions** are made in U^{−ε}, V^{−ε}, (εX/e)^ε, L²/U and Δ.

**Sanity checks (non-rigorous).**
- The model gives S ≈ ½ + (xL − γ − vL)/Δ: 1.63 at e^29, 2.4 at e^80.
- `ref/bv.py`: 1.98 computed against 2.17 from the model.
- `explore/chain_check.py`: a direct computation gives S − 1 = 1.08, below the chain's 2.62.
- The table of M agrees with mpmath to 16 digits.
- The rigorous bound is within 3.4% of the model on every row.

**Numbers with her (u, v, x)** (`results/d4_rows.json`):

| row | d₄ Bellotti | **d₄ Lemma A** | ratio |
|---|---|---|---|
| 28.73–29 | 84.80 | **4.414** | 0.052 |
| 46.2–50 | 106.11 | 5.099 | 0.048 |
| 60–70 | 128.20 | 5.690 | 0.044 |
| 70–80 | 146.70 | **6.105** | 0.042 |
| 80–90 | 162.54 | **6.437** | 0.040 |
| 100–110 | 181.45 | **6.767** | 0.037 |
| 160–170.2 | 235.58 | 7.662 | 0.033 |

On Phase 0's re-optimised rows (RO0001, RO1205, RO1379, RO1505), d₄ falls from 95.25 / 124.75 / 143.51 / 185.03 to 4.503 / 5.259 / 5.693 / 6.523.

## 2. Lemma B: zeros in a box next to the 1-line

**Hypotheses.**
- t₀ − h/2 ≥ 3·10¹², T ≥ t₀ + h/2, and β ≤ 1−ν for every zero with 0 < γ ≤ T.
- The box is B = {β+iγ : 1−δ ≤ β ≤ 1, |γ−t₀| ≤ h/2}.
- 0 < r < ½ and √((r+δ)² + h²/4) < ½.
- P(θ) = a₀ + cos θ + Σ_{k≥2} a_k cos kθ ≥ 0, with a_k ≥ 0.

**Statement.** With BTZ(r, ℓ) = (ℓ + 4.709774)/(4+8r) + (4/π−1)log(1+1/r)/(1+2r) + 2.6908 and c_min = min_{X∈[r+ν, r+δ]} X/(X²+h²/4),

#B·(c_min − 4(r+δ)/(1+2r)²) ≤ a₀(−ζ′/ζ)(1+r) + Σ_{k≥2} a_k(BTZ(r, log kT) + 10⁻²⁴) + BTZ(r, log T) + 10⁻²⁴.

**Proof.**
1. Apply Heath-Brown (PLMS 64 (1992), Lemma 3.2) to f(z) = ((z−1)/(z+1))ζ(z) on a disc of radius r₁ ∈ (½, ½+r) around s = 1+r+it₀. The zero sum is positive.
2. For ρ ∈ B, Re 1/(s−ρ) ≥ c_min, because X/(X²+h²/4) is unimodal.
3. Thorner–Zaman (Forum Math. 36 (2024)), inside the proof of Prop 2.11: in the limit, −J ≤ BTZ(r, log T). This uses Hiary–Patel–Yang 0.618 through Prop 2.10.
4. Put θ = t₀ log n into P ≥ 0, weight by Λ(n)n^{−1−r}, and sum.
5. Steps 1–3 at 1+r+ikt₀ bound the k-terms. ∎

With a₀ = 1, a_k = 0 and the disc geometry, Lemma B reduces to Bellotti's Cor 2.3. The gain comes from two places:
- the evaluation point 1+ρδ+it₀ with ρ ≈ 2.6;
- a₀ ≈ 0.63.

**Numbers.**
- K = 3, with coefficients chosen per row by LP and rounded to fractions. P ≥ 0 is certified in Arb with margin ≥ 2·10⁻⁴.
  - Example at e^29: a₀ = 6309/10000, a₂ = 1201/2500, a₃ = 1111/10000, ρ = 51/20.
- cf = sup #B/(δ log T) over δ ∈ [ν(T), 1−α₀] and the row.

| row | Bellotti b₁ + b₂Z₀ | **cf** | ratio |
|---|---|---|---|
| 28.73–29 | 12.457 | **7.457** | 0.599 |
| 46.2–50 | 12.699 | 7.107 | 0.560 |
| 70–80 | 11.699 | 6.329 | 0.541 |
| 80–90 | 11.422 | 6.129 | 0.537 |
| 100–110 | 10.899 | 5.840 | 0.536 |

For tall boxes the gain shrinks: the ratio to the Thorner–Zaman disc count rises from about 0.60 at λ = 1 to about 0.79 at λ = 13.

**Inputs.**
- Heath-Brown Lemma 3.2 (refereed).
- Thorner–Zaman (refereed). We use the inequality on −J that is proved inside the proof of Prop 2.11 (arXiv:2208.11123v4, pp. 7–8), not the statement of the proposition.
  - The ordinate shift on the circle costs less than 10⁻¹², against a margin of 2.6·10⁻⁵. This is our inference.
- Hiary–Patel–Yang (refereed).
- Delange's rZ(r) < 1, used only in the affine b₂.

## 3. Lemma C: the factor 2 in (4.6)

**Statement.** Let z = 2 − ρ_r − ρ̄_s = y − ia, with y ∈ [2ν, 2δ] and 1 < Y = U/L² < X. Then
- (i) |X^z − Y^z| ≤ (1+κ)X^{2δ}, with κ = (Y/X)^{2ν};
- (ii) |Γ(z)(X^z − Y^z)| ≤ Γ(1+y)(X^y − Y^y)/y ≤ X^{2δ}(1 − (Y/X)^{2δ})/(2δ).

**Proof of (ii).** X^z − Y^z = z∫e^{zτ}dτ, |Γ(z)z| = |Γ(1+z)| ≤ Γ(1+y) ≤ 1, and (X^y − Y^y)/y is increasing in y. ∎

**Use.**
- c₂ is multiplied by f₂ = min{(1+κ)/2, (1 − (Y/X)^{2(1−α₀)})/2.0134}.
- c₃ and c₄ are multiplied by f₃₄ = (1+κ)/2.
- (ii) also removes the step "X^{2−y}/(2−y) decreasing", which fails near e^{170}.
- κ needs ν to be decreasing. For the Ford region, dν₂/dL ≤ −6.9·10⁻⁶ on [28, 172] is certified in Arb.
- Phase 0 found (i) independently; (ii) is new.

| row | κ | factor on c₂+c₃+c₄ |
|---|---|---|
| 28.73–29 | 0.158 | 0.569 |
| 46.2–50 | 0.332 | 0.653 |
| 70–80 | 0.446 | 0.708 |
| 80–90 | 0.476 | 0.723 |
| 100–110 | 0.514 | 0.741 |

## 4. Effect on C (her parameters; float model)

C = (c₂+c₃+c₄)·cf/(c₁² − c₅). Lemma A scales c₂, c₃, c₄ and c₅.

| row | C printed | A | B | C | **A+B+C** | C estimate |
|---|---|---|---|---|---|---|
| 28.73–29 | 37 342 | 0.0489 | 0.599 | 0.569 | **0.0166** | 621 |
| 46.2–50 | 104 761 | 0.0445 | 0.560 | 0.653 | 0.0163 | 1 705 |
| 70–80 | 278 045 | 0.0378 | 0.541 | 0.708 | **0.0145** | 4 029 |
| 80–90 | 370 656 | 0.0357 | 0.537 | 0.723 | **0.0139** | 5 135 |
| 100–110 | 488 901 | 0.0337 | 0.536 | 0.741 | **0.0134** | 6 536 |

**Caveats.**
- The factors are relative to her printed C, which Phase 0 shows is about 2× too small.
- On Phase 0's rows, expect about ×0.03–0.04 before re-optimisation.
- With d₄ 20–30× smaller, the optimal parameters, and B = 2x in particular, will move. The re-optimisation belongs to Phase 0; use `d4_model` as the fast stand-in during the search.

## 5. Interface (`improvements.py`)

Every function here is rigorous and returns Arb balls.

| Function | Use |
|---|---|
| `d4_upper(u, v, x, logT_lo, logT_hi)` | Lemma A |
| `cf_upper(alpha0, nu, logT_lo, logT_hi, hfac)` | Lemma B, with hfac = λ |
| `count_upper(...)` | Lemma B as (b₁, b₂) |
| `residue_factors(...)` | Lemma C as (f₂, f₃₄, κ) |
| `pair_residue_bound(...)` | Lemma C, per pair |
| `d4_model` | float, not rigorous |

**Integration hook.** In `belarb.py`, replace `opt['d4']` by `d4_upper` over the same range of T.

## 6. Notes on Bellotti

- In (3.20), "Ψ(n) = Λ(n)/log(V/U) for n > U" is false, but the term is harmless.
- Her code's d₃ is missing a factor L².
- The square in Lemma 2.4 has height 2δ while the boxes have height δ, so it safely over-counts.

## 7. Not done, or did not work

- A Rankin majorant built from several exponentials gives no gain.
- A Weyl-exponent version of Lemma B is not done; the estimated further gain is 5–7%.
- Item 4 (smoother weights, F ≈ 15) is not attempted: Lemma 3.4 and c₅ would have to be redone. It is low priority because the gain from C alone saturates.


## Round 2 addendum (saved by the main session from the sub-agent's final message)

### Verdicts

| Item | Status | Effect on C·e^{B/4.62} | Tier |
|---|---|---|---|
| Item 4 (smooth weights) | **Infeasible**: every smoothing width is a net loss | worse by 4–109%, depending on the width | — |
| **Lemma D** (new): the mollifier on Re s = ½ inside c₁ | **Fully proved, Arb-verified** | ×0.29 at e^29; ×0.33–0.38 at e^35–e^41 | own lemma; elementary inputs only |
| **Lemma B-W**: the Weyl exponent in Thorner–Zaman's −J bound | **Fully proved, Arb-verified**, given the quoted inputs | cf ×0.97 at e^29 down to ×0.90 at e^100 | own lemma + refereed inputs |
| Reviewer's small fixes | Applied | none | — |

### Lemma D

**Statement.** Take 1 ≤ U < V, W > 1, Δ = log(V/U), Q(y) = Σ_{m≤y} μ²(m)m^{−½}, c = sup Q(y)/√y, and P* = Π_p(1 + p^{−3/2} − p^{−2}). Then

|M(½+it)| ≤ Σ_{v,w}|ψ_v||θ_w|[v,w]^{−½} ≤ (4c²P*/(Δ log W))(V^{½} − U^{½})(W^{½} − 1).

The constants are c = Q(7)/√7 = 1.3296349…, P* ≤ 1.47523, and 4c²P* ≤ 10.4324.

**What it replaces.** Bellotti bounds the same quantity by d₂(VW)^{½}log⁴(VW), and Phase 0 uses D2VW·(VW)^{½}. At e^29 the new factor K_D is about 0.00997, against about 1.2·10⁷ before.

**Proof sketch.**
- Write [v,w]^{−½} = (vw)^{−½}Σ_{δ|(v,w)}φ_{½}(δ).
- Express |ψ| and |θ| as integrals over thresholds, which gives A_δ ≤ 2c(V^{½} − U^{½})/(Δδ) and B_δ ≤ 2c(W^{½} − 1)/(δ log W).
- Finally, Σ_δ μ²(δ)φ_{½}(δ)/δ² = P*.

**Auxiliary results.**
- D.1: c is attained at m = 7. This was checked in Arb for m ≤ 10⁶; for larger m, D.2 applies.
- D.2: Q(y) ≤ (12/π²)√y + 1.5 log y + 2.4.
- D.3: P* is an Arb product over p ≤ 10⁶, plus a tail bound.

**Brute-force check.** The ratio bound/S_abs lies between 1.45 and 1.66.

**Plug-in.** In `piece_v2`, set SU = K_D/(2π)·(…) in place of D2VW. For a ball of L values, use K_D = 4c²P*(1 − e^{−Δ/2})(1 − e^{−wL/2})/(Δ·wL).

**Rigorous rows** (cl4.896; lemmas A, B-W, C, D):

| Row | C | B | C·e^{B/4.62} | Phase 0 v2 |
|---|---|---|---|---|
| [log 3e12, 29] | ≤ 127.58 | 9.672 | 1035 | 3615 |
| [35, 36] | 132.22 | 9.148 | 958 | — |
| [40, 41] | 132.24 | 8.838 | 896 | — |

These were produced by `certify_lemmaD_demo.py`, which patches `piece_v2` at runtime.

**Suggestion.** Using Hiary–Patel–Yang's 0.618 in place of 66.7·t^{27/164} in c₁'s I2c could lower B by about 0.18, i.e. about 4%.

### Lemma B-W

**Statement.** limsup(−J) ≤ ((1/6 + η)ℓ + log A_η)/(1+2r) + (4/π − 1)log(1 + 1/r)/(1+2r) + 2.6908, where:
- ℓ = log(√2 T);
- A_η = max(1.461, 0.618/(eη));
- the side condition A_η e^{105(2/984+η)} ≥ 66.7 holds;
- η = 1/ℓ.

**Proof outline.**
- The bound |ζ(½+iy)| ≤ A_η|1+iy|^{1/6+η} combines:
  - the Arb bound 1.461 for |y| ≤ 3;
  - Hiary–Patel–Yang for 3 ≤ |y| ≤ e^105;
  - Patel–Yang beyond e^105.
- Apply Rademacher's Phragmén–Lindelöf lemma to ((z−1)/(z+1))ζ(z) on ½ ≤ σ ≤ 1 + r.
- Integrate over the left arc as in Thorner–Zaman's J₃.
- The bound J₁ + J₂ + J₄ + J₅ ≤ 2.6908 is unchanged.

**Inputs.** Rademacher, Math. Z. 72 (1959), statement as usually quoted (UNSURE on the exact wording); Hiary–Patel–Yang; Patel–Yang; Thorner–Zaman (an inequality from inside their proof).

**Sanity check.** At t = 1000 and 5000, the actual −J lies between −0.30 and −0.11, against bounds of 5.9–6.9.

**Effect on cf.** ×0.98 / 0.97 at e^29 (λ = 1 / λ = 18); ×0.89–0.94 at e^100.

### Item 4: why it is infeasible

- The weight is φ_X − φ_Y, with φ_X(n) = ∫e^{−ne^s/X}dν(s), where ν is a bump of log-width H. Its Mellin transform is Γ(z)(X^zν̂(z) − Y^z).
- The band term gains |ν̂(a)|, but only once |a|H ≳ 1–2.
- The detector's integral term costs X·e^{−H_eff}, with H_eff ≈ 0.57H. That raises B by about 2H_eff/L.
- At λ ≈ 14–18 the band sum is only 25–30% of Hn.
- Net result: every width loses. At e^29, H = 3 gives 1203 against 1145, H = 10 gives 1324, and H = 40 gives 2392.
- The round-1 claim that smoothing could bring F from 15 down to 2–3 is retracted.

### Interface additions

- `improvements.mollifier_half_line_KD(u, v, w, logT_lo, logT_hi=None)`
- `cf_upper(..., weyl=True)`
- `lemmaB_weyl.BTZW`
- `lemmaD_mollifier.S_abs_bound`

### Files

- `lemmaD_mollifier.py` (8 s), `lemmaB_weyl.py` (2 s), `certify_lemmaD_demo.py` (2 min).
- `explore/round2_*.py` and their outputs: float models.
- `explore/lemmaD_check.py`, `explore/jcheck.py`.

### Round-2 review notes (work/review_round2/REVIEW.md), recorded by the main session

**Verdicts.** Lemma D, Lemma B-W and the local classical constants: all CONFIRMED.

**Lemma D.2.** The report gave no proof. The reviewer supplied a sufficient replacement:

Q(y) ≤ (12/π²)√y + 2√y/⌊√y⌋ + 2 + log y.

This gives Q(y)/√y ≤ 1.2337 < c for y > 10⁶, so the constant c = Q(7)/√7 is unaffected.

**`lemmaB_weyl.A_eta`.** `float(x.upper())` rounds to the nearest float, so A_η can come out 1 ulp low. This must be fixed by rounding upward or keeping the value as an arb. The ×(1+10⁻⁹) inflation applied to cf in the drivers currently absorbs the error.

**`certify_lemmaD_demo.py`.** The script no longer runs, because Phase 0 integrated Lemma D directly into `piece_v2`. The reviewer reproduced row 1 exactly (C ≤ 127.584) with Phase 0's built-in version.

**Possible extra gain (not yet verified in code).** Lemma D with U = 1 applied to G(½+it) in c₅ would replace the factor 16 by 4c² ≈ 7.07.
