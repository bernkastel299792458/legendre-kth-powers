# Referee review of Phase 2 (`work/phase2_lemmas/`): Lemmas A, B, C

*Independent second reader, 2026-11-06. Sources read: `phase2_lemmas/REPORT.md` and the code. Primary texts:*
- *Bellotti — `ref/bel_v2.txt`;*
- *RZA identity factory — TeX of arXiv:2312.05138 v1, v2 and v3 in `phase2_lemmas/lit/`;*
- *Thorner–Zaman — TeX (V2) and `ref/thorner_zaman_2208.11123.txt` (v4);*
- *Heath-Brown 1992 — `lit/HeathBrown_1992_PLMS_linnik_ORA.txt`.*

*Nothing outside `work/review_phase2/` was modified.*

## Verdicts

| # | Item | Verdict |
|---|---|---|
| 1 | Lemma A, (A1): the diagonal inequality | **CONFIRMED** |
| 1′ | S is exactly Bellotti's first factor in (4.3), and ψ_d is exactly her (3.1) | **CONFIRMED** |
| 2 | Lemma A, (A2): Rankin, and Ψ(n) = 0 for 2 ≤ n ≤ U | **CONFIRMED** |
| 3 | Lemma A numerics: the RZA input, the table, `lemmaA_d4.py` | **CONFIRMED** (small robustness nits, below) |
| 4 | Lemma B: the box count | **CONFIRMED**, conditional on accepting TZ's in-proof inequality (checked against the source); one citation is wrong |
| 5 | Lemma C: the residue factor | **CONFIRMED**. One latent invalid branch, which is never selected |
| 6 | Other | No error that changes any number. Notes below |

**Most serious problem found.** There is no fatal error. The issue most likely to bite later is in Lemma C.
- **Where:** `lemmaC_residue.py`, `residue_factors`: `f2 = min(f34, fd)`. The module docstring and REPORT §3 ("c₂ is multiplied by min{(1+κ)/2, …}") say the same.
- **The problem:** the (1+κ)/2 option for c₂ is not justified in general.
  - It needs Bellotti's step "X^y/y is increasing on [2ν, 2δ]", i.e. 2ν·log X ≥ 1.
  - On her rows that condition fails for L ≥ 100: there 2ν·log X = 0.83–0.99 (my computation).
- **Why it is harmless now:** the min always selects the (ii) branch, so no current number is affected. Since κ ≥ 0, (1+κ)/2 ≥ 1/2, while the (ii) factor is (1 − (Y/X)^{2(1−α₀)})/2.0134 < 1/2.0134 < 1/2.
- **Fix:** drop the branch and set f₂ := the (ii) factor.

**Can `improvements.py` be trusted as an input?** Yes, with conditions:
- **`d4_upper`:** rigorous. I validated it three independent ways (below).
- **`cf_upper` / `count_upper`:** rigorous, provided:
  - TZ's in-proof bound on −J is accepted as an input;
  - the caller supplies boxes with t₀ − h/2 ≥ 3·10¹² and t₀ + h/2 ≤ T. A box straddling 3·10¹² must be shifted up; this is legitimate, because RH is verified below that height;
  - any user-supplied ν is a valid, decreasing zero-free width.
- **`residue_factors`:** rigorous for ν = "classical" or "ford" with log T ≤ 172. Monotonicity of ν₂ is certified only on [28, 172].
- **`d4_model`, and the C assembly in `effect_on_C.py`:** floats, not rigorous. The REPORT says so too.

---

## 1. Lemma A, (A1): re-derivation

**Definitions against Bellotti (the paper states).**
- (3.1) defines ψ_d as:
  - μ(d) for d ≤ U;
  - μ(d)·log(V/d)/log(V/U) for U < d ≤ V;
  - 0 for d > V.
- REPORT's g(d) = (log⁺(V/d) − log⁺(U/d))/Δ gives 1, log(V/d)/Δ and 0 on the same three ranges, so the two definitions are identical.
- (3.8) sets U = T^u, V = T^v, X = T^x, L = log T.
- Lemma 4.2 bounds the first factor of (4.3), Σ_n Ψ²(n)n⁻¹(e^{−n/X} − e^{−nL²/U}). This comes from Lemma 2.12 with ξ_n = Ψ(n)w(n)^{1/2}n^{−1/2}.
  - Ψ appears squared; Θ goes into φ_r and not into this factor.
  - This is exactly the S of Lemma A.
- c₂, c₃, c₄ and c₅ are all linear in d₄: c₅ appears at line 2056 of `bel_v2.txt`. So scaling all four by the ratio of d₄ values, as the effect model does, is consistent with her formulas.

**Steps (my own derivation).** Write s = 1 + ε, with ε > 0.
1. **Opening the square.** Σ_n Ψ(n)²n^{−s} = Σ_{d,e} ψ_dψ_e Σ_{[d,e]|n} n^{−s} = ζ(s)Q. The sums over d and e are finite (d, e ≤ V), so the interchange is fine.
2. **Diagonalising.** [d,e]^{−s} = (de)^{−s}(d,e)^s, and (d,e)^s = Σ_{δ|(d,e)} φ_s(δ), with φ_s = μ⋆N^s, so φ_s(n) = n^sΠ_{p|n}(1 − p^{−s}) > 0. Hence Q = Σ_δ φ_s(δ)y_δ², where y_δ = Σ_{δ|d} ψ_d d^{−s}. If δ is not squarefree, then y_δ = 0, because ψ is supported on squarefree d.
3. **Squarefree δ.** y_δ = δ^{−s} Σ_m μ(δm)g(δm)m^{−s} = μ(δ)δ^{−s}F_δ, where F_δ = Σ_{(m,δ)=1} μ(m)m^{−s}g(δm). This is a finite sum, since g(δm) = 0 for δm ≥ V.
4. **Removing the coprimality condition.**
   - *The identity.* μ(m)1_{(m,δ)=1} = Σ_{jk=m, k|δ^∞} μ(j) is a pointwise identity: for each m the sum runs over divisors of m only, so there is no convergence question. It follows from the Euler factors Π_{p∤δ}(1 − p^{−s}) = Π_p(1 − p^{−s})·Π_{p|δ}(1 − p^{−s})^{−1}. I also checked it exhaustively for squarefree δ ≤ 300 and m ≤ 3000 (`identity_check.py`): 0 violations.
   - *The rearrangement.* The double sum over (j, k) is finite: k|δ^∞ with δk < V, and j < V/(δk).
   - *The inner sum.* Σ_j μ(j)j^{−s}log⁺(Y/j) = M(Y) holds for every real Y. Indeed log⁺(Y/j) = log(Y/j) when j ≤ Y and 0 otherwise, and M(Y) = 0 for Y < 1 by definition. So no integrality of Y is needed.
   - *The case δk ≥ V.* All terms g(δkj) vanish, and H(δk) = M(V/δk) − M(U/δk) = 0 − 0. So that case is handled correctly.
   - *Result.* F_δ = Δ^{−1}Σ_{k|δ^∞} k^{−s}H(δk) is correct.
5. **Cauchy–Schwarz.** Use weights k^{−s} over k|δ^∞ (only finitely many H(δk) ≠ 0). Then Σ_{k|δ^∞} k^{−s} = Π_{p|δ}(1 − p^{−s})^{−1} = δ^s/φ_s(δ). This gives φ_s(δ)y_δ² ≤ Δ^{−2}Σ_{k|δ^∞}(δk)^{−s}H(δk)².
6. **The bijection.** Suppose n = δk with δ squarefree and k|δ^∞. Every prime of n then divides δ, and δ|n is squarefree, so δ = rad n is forced. I checked uniqueness exhaustively for n ≤ 3000.
7. **Conclusion.** Also H(n) = 0 for n ≥ V, because M(1) = 0. Hence (A1) holds. ∎

**Numerical test of (A1) (`bf_lemmaA.py`; float64 with exact Möbius values).**
- The left side ζ(s)Q was computed from the exact double sum over squarefree d, e ≤ V. I checked that code at s = 2 against the direct sum Σ_{n≤N}Ψ²n^{−2}: agreement to 10⁻⁹.
- Cases: (U, V) = (50, 2500), (100, 10⁴), (200, 4·10⁴), (60, 60^{2.5}), each with ε ∈ {0.02, …, 0.13}.
- (A1) holds in all 24 cases. RHS/LHS lies between 1.04 and 1.21, and it decreases as U grows, consistent with "sharp to first order".

## 2. Lemma A, (A2)

- Ψ(1) = ψ₁ = 1.
- For 2 ≤ n ≤ U, every divisor of n is ≤ U, so Ψ(n) = Σ_{d|n} μ(d) = 0. Bellotti states the same after (3.1).
- w(1) = ∫_{1/X}^{L²/U} e^{−t}dt ≤ L²/U.
- For n > U: w(n) ≤ e^{−n/X} ≤ (ε/e)^ε(X/n)^ε, since sup_y y^εe^{−y} = (ε/e)^ε. Hence S ≤ L²/U + (εX/e)^ε(ζ(s)Q − 1).
- **A check the REPORT omits:** the code substitutes the *upper* value (εX/e)^ε with X = e^{xL_b}. That is valid only because the bracket is ≥ 0, which holds since ζQ ≥ Ψ(1)² = 1. So the direction is correct.
- **Brute-force test.** S was summed directly to N = 45X, with Y = U/L² and L ∈ {2, 2.5, 3}, at the four scales above. S ≤ the (A2) bound in every case. Example, U = 200: S = 1.262, against a best bound of 2.87.

## 3. Lemma A numerics

**The RZA input (paper states; arXiv v3, theorem `mcheckqeps`, `lit/src_2312.05138/…-18.tex`, lines 431–453).**
- The theorem: for σ = 1+ε ∈ [1, 11/10] and real X ≥ 15, M(X) = log X/ζ(σ) − ζ′/ζ²(σ) + Δ̌/X^ε, with
  - |Δ̌| ≤ 0.0336·g₁·2^ε·(q^ξ/φ_ξ)·1_{X≥10¹²}/log X + (4.86·g₀ + 2.93 + 2.83ε log X + 5.17ε)·(√q/φ_{1/2})·2^ε/√X.
- At q = 1 we have g₀ = g₁ = 1 and both q-ratios equal 1 (from `defg0g1`, lines 375–386). So the REPORT and the code (7.79 = 4.86 + 2.93) are exact transcriptions.
- I re-derived parts of the proof:
  - √8·2^ε(2 − 1/(1+ε))²/log 2 ≤ 4.86·2^ε at ε = 0.1;
  - 0.010333 × that factor ≈ 0.0177, below the stated 0.0336, so the stated constant is conservative.
- **Version history.** v2 has the same constants. v1 had 0.0256, so the constant was raised, not lowered.
- **Not checked (UNSURE):** the journal text, as the REPORT says. The input depends on Helfgott's |m(t)| ≤ √(2/t), through `boundmqdex`.

**`lemmaA_d4.py`, read line by line. These items are correct:**
- **`rbar`:** r_small is decreasing in log y, and r_big is decreasing on [log 10¹², ∞). So max(r_small(ℓ), r_big(log 10¹²)) is a valid majorant below 10¹². It asserts ℓ ≥ log 15.
- **The table:**
  - it is computed in Arb at 110 bits;
  - the doubles are rounded outward with nextafter;
  - M is continuous and monotone on each [k, k+1), with M(y) = P_k log y − Q_k. So the range over a block is attained at the endpoints and the interior integers, which is what `range_log` does;
  - the ±10⁻¹² widening of the float exponentials covers rounding;
  - the table and analytic parts overlap, and leave no gap.
- **Region 0 (n ≤ N₁):** H = BΔ + R − R, with both arguments ≥ U/N₁ ≥ Y₀ (asserted at L_a).
- **Region I (N₁ < n ≤ U):**
  - the n-integral of each block equals U^{−ε}(e^{εw_b} − e^{εw_a})/ε exactly;
  - Σ_{a≤n≤b} f ≤ ∫_a^b f + f(a − 1) for decreasing f is correct;
  - (a − 1)^{−s} ≤ 2/a needs a ≥ 2. This is not asserted (nit), but a ≥ N₁e^{−u·0.25} ≥ 58 for all parameters in use;
  - the four-corner range of K/Δ over Δ ∈ [Δ_a, Δ_b] is correct.
- **Region II (U < n < V):** the argument of M(U/n) is w′ − Δ ∈ [w_a − Δ_b, w_b − Δ_a].
- **Coverage:** blocks running past n = N₁ or n = U for smaller L only double-count non-negative terms.
- **Monotone substitutions:** U^{−ε} and V^{−ε} at L_a; (εX/e)^ε at L_b; L²/U as L_b²/e^{uL_a}; Δ at Δ_a for the error terms.

**Independent numerical validation (my scripts):**
1. **`test_Tbound.py`: their `T_bound` against the exact Σ_{n<V} n^{−s}H²/Δ²**, at U ≈ 5·10³–2·10⁵ and V ≈ 5·10⁶–8·10⁶.
   - It is ≥ the exact value in every case, both pointwise and uniformly over L ∈ [10, 10.25].
   - With the RZA term the bound is loose at this scale, because 7.79/√y is large for small y.
   - With the RZA term replaced by the true sup|R| (non-rigorous, as a tightness test), T_bound is 1.4–5.0% above the exact value. So no region is missing and no direction is wrong.
2. **`truescale_float.py`: the expression Lemma A bounds, at the true scale**, computed from scratch. It uses the integral form, which is very accurate for n > 10⁵, the exact M table up to 10⁶, and A + B log y beyond.

   | row | my float value of the expression | their rigorous bound | excess |
   |---|---|---|---|
   | e^{28.73}–e^{29} | 4.258 / 4.260 | 4.414 | +3.6% |
   | 46.2–50 | 4.912 / 4.932 | 5.099 | +3.4–3.8% |
   | 80–90 | 6.272 / 6.311 | 6.417 / 6.437 | +2% |
   | 160–170.2 | 7.537 / 7.558 | 7.640 / 7.658 | +1.3% |

   ζ·Q on row 1: 1.740 here, against 1.767 in their output.
3. **`sens_rbar.py`:**
   - It reproduces the stored row-1 value, d₄ ≤ 4.413667.
   - Multiplying the RZA error term by 10 raises d₄ by 2.86%, as the REPORT says (2.9%).

**What I infer.** The ~20× gain over Bellotti's d₄ is real. Her d₄ ≈ 84.8 on row 1 comes almost entirely from the RZA Corollary 1.2 term, 3.09·(u+v)/(v−u)·9.47 ≈ 84.8; I recomputed this.

## 4. Lemma B

**Heath-Brown, Lemma 3.2 (source text, lines 577–585).** Re f′/f(a) = −Σ n_k(r_k^{−1} − r_kR^{−2})cos θ_k + (πR)^{−1}∫cos θ·log|f(a + Re^{iθ})|dθ.
- With s − ρ = −r_ke^{iθ_k}, this becomes −Re f′/f(s) = −Σ Re(1/(s−ρ) − (s−ρ)/r₁²) − J, which is TZ's form.
- Take f = ((z−1)/(z+1))ζ(z). It is holomorphic on the disc, since the pole at −1 is far away.
- Each zero term equals Re(s−ρ)(|s−ρ|^{−2} − r₁^{−2}) > 0. So dropping zeros outside B is legitimate.

**The chain I re-derived.**
1. For ρ ∈ B, Re 1/(s−ρ) = X/(X²+Y²) ≥ X/(X²+h²/4) ≥ c_min. The map X ↦ X/(X²+a²) is unimodal, so the minimum over [r+ν, r+δ] is attained at an endpoint.
2. Also Re(s−ρ)/r₁² → ≤ 4(r+δ)/(1+2r)² as r₁ → ½ + r.
3. Since Λ ≥ 0 and P ≥ 0: a₀(−ζ′/ζ(1+r)) + Re(−ζ′/ζ(s)) + Σ_k a_k Re(−ζ′/ζ(s_k)) ≥ 0. With a_k ≥ 0, this gives Re ζ′/ζ(s) ≤ a₀(−ζ′/ζ)(1+r) + Σ_k a_k Re(−ζ′/ζ(s_k)).
4. Re(−ζ′/ζ(s_k)) ≤ Re 2/(s_k² − 1) − J_k ≤ 10⁻²⁴ + (−J_k). This uses TZ with t = kt₀ and "T" = kT.
5. Taking r₁ → (½ + r)⁻ along radii that avoid zeros gives the stated inequality.

**The TZ input (paper states).** In the proof of Prop. 2.11 (TeX line 703; v4 text line 546), TZ write lim_{r₁→(r+½)⁻}|J| ≤ (log(qT) + 4.709774)/(4+8r) + (4/π − 1)log(1 + r^{−1})/(1+2r) + 2.6908.
- Lemma B needs only an upper bound on −J. That is the direction TZ's argument naturally gives:
  - J₃ is bounded through an upper bound on log|F|;
  - J₁,₂,₄,₅ are bounded two-sidedly through |log|ζ(σ+it)|| ≤ log ζ(σ), with the factor log|(z−1)/(z+1)| = O(10⁻¹²).
- **I infer that there is margin:**
  - The true sup over r of TZ's J₁ + J₂ integral is 1.2199, against the 1.3454 they use (my quadrature).
  - The decomposition 4.709774 = 4·1.0908 + ½ log 2 suggests the |1 + iy| versus T slack is built in.
  - For ζ at t ≥ 3·10¹², 0.63t^{1/6}log t ≤ 0.56·e^{1.0908}t^{1/4}.

  So the ordinate shift on the circle is harmless.
- **Citation error (bookkeeping only).** The REPORT says that this "uses Hiary–Patel–Yang 0.618 through Prop 2.10". TZ v4 (TeX `\cite{Hiary}`, bbl line 71) uses **Hiary, Indag. Math. 27 (2016), 0.63|t|^{1/6} log|t|**. Hiary 2016 is refereed too, and either bound suffices. The input-status tag should be corrected.

**Checks in code.**
- The geometry √((r+δ)² + h²/4) < ½ and r < ½ are asserted for every (λ, L) block.
- My runs, all assertions passing:

  | case | ρ | max r + δ | h/2 | cf |
  |---|---|---|---|---|
  | λ = 1, row 1 | — | — | — | 7.4564 |
  | λ = 13, row 1 | 10.58 | ≈ 0.085 | ≈ 0.047 | 13.43 |
  | λ = 13, Ford 80–90 | — | — | — | 10.85 |

- **Trigonometric polynomials.** The exact-cubic certification and a dense sampling with 2·10⁶ points both give min P = 2·10⁻⁴ for the row-1 polynomials (both the REPORT's and my rerun's), and 2.3–2.8·10⁻⁴ for the λ = 13 ones.
- **Monotone substitutions.** The numerator is decreasing in r and increasing in L. For the denominator, δ·c_min ≥ min(φ(ρ+e_lo), φ(ρ+1)) with e = ν/δ ≥ λ_min/λ_hi.
- **Nit:** `b1b2_upper` takes λ_min by sampling 41 points. That is valid for the three built-in ν, because νL is monotone, but not for arbitrary callables.
- **Nit:** the LP is re-solved on every run. My rerun gave a₀ = 6307/10000, a₂ = 4809/10000, a₃ = 557/5000, ρ = 127/50, against the REPORT's 6309/10000, 1201/2500, 1111/10000, 51/20. Both are certified, so this does not matter.

**Input status:**
- our own lemma;
- Heath-Brown, PLMS 1992 (refereed);
- Thorner–Zaman, Forum Math. 2024 (refereed), using an in-proof inequality that I checked in the source;
- Hiary 2016 (refereed);
- Delange, for b₂ only;
- the zero-free regions.

## 5. Lemma C

**Proof re-derived.**
- (i) |X^z − Y^z| ≤ X^y(1 + (Y/X)^y) ≤ X^{2δ}(1+κ), since y ∈ [2ν, 2δ] and Y < X.
- (ii) X^z − Y^z = z∫_{log Y}^{log X}e^{zτ}dτ.
  - |Γ(z)z| = |Γ(1+z)| ≤ Γ(1+y) ≤ 1 for y ∈ [0, 1].
  - (X^y − Y^y)/y = ∫e^{yτ}dτ is increasing in y because log Y > 0.
  - Hence the bound X^{2δ}(1 − (Y/X)^{2δ})/(2δ), and δ ≤ 1 − α₀.

**Bellotti's c₂ (paper states).** c₂ = 1.0067·d₄d₅/w, from (4.7)–(4.10). The "2" of (4.6) cancels against 1/(2δ). So the (ii) factor relative to c₂ is (1 − (Y/X)^{2(1−α₀)})/2.0134, as the code has it.

**Bellotti's own c₂ step (I infer).** It needs X^y/y to be increasing on [2ν, 2δ], i.e. 2ν·log X ≥ 1, and that fails on her rows L ≥ 100. Phase 2's (ii) repairs this.

**The latent invalid branch.** The (1+κ)/2 option for c₂ inherits the same flaw. As noted at the top, it is never selected; remove it.

**c₃ and c₄.** Using (1+κ)/2 is valid: those cases use |z| ≥ |γ_r − γ_s|, and X^y ≤ X^{2δ}.

**κ.** κ uses ν(γ) ≥ ν(T), which needs ν decreasing. That is certified for Ford on [28, 172] only.

## 6. Other remarks

- **Effect on C.** `effect_on_C.py` is a float model relative to Bellotti's printed C. It is an effect estimate, not a certified C (the REPORT says the same).
  - The Phase 0 issue (the counting gap: neighbouring boxes and both sides) is independent of Lemmas A and C.
  - Lemma B with tall boxes λδ is the intended route for that issue. Lemma A does not depend on the boxes.
- **REPORT §6, on Bellotti (3.20).** Ψ(n) = Λ(n)/log(V/U) for n > U is indeed false. The divisors d ≤ U carry weight μ(d), not μ(d)log(V/d)/Δ.
  - I agree that it is harmless: the weight e^{−nL²/U} ≤ e^{−L²} ≈ e^{−825} kills the term even with the trivial bound |ΨΘ| ≤ τ(n)². This is my inference.
- **Robustness nits:**
  - assert a_j ≥ 2 in `T_bound`;
  - make `b1b2_upper`'s λ_min an interval evaluation;
  - make `residue_factors` refuse log T > 172 unless dν/dL < 0 has been certified there.

## Files in this folder (re-run)

| file | what | runtime |
|---|---|---|
| `bf_lemmaA.py` → `bf_lemmaA.out` | brute-force S, exact double-sum ζQ, (A1) and (A2) at U = 50–200 | ~10 min |
| `test_Tbound.py` (no arg / `tight` / `tight2`) | their `T_bound` against the exact sum at moderate scale; tightness with the true R | ~10–30 s each |
| `truescale_float.py` [rows JSON] | independent float value of the Lemma-A expression at true scale | ~15 s per row |
| `sens_rbar.py` | reproduces the row-1 d₄; sensitivity to the RZA term ×10 | ~2 min |
| `identity_check.py` | exhaustive check of the coprimality-removal identity and of the bijection | ~1 min |

All scripts are float exploration or referee checks. None of them is a claimed bound.
