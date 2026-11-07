# Referee report: local classical zero-free region on log t ∈ (28.7296, 60] (`zfr_classical_local.csv`)

**Object under review** (`work/phase1_littlewood/`): `cl_core.py`, `check_cl.py` → `check_cl_output.txt`, `cl_constants.json`; `cert_classical.py` → `zfr_classical_local.csv`, `cert_classical_summary.json`, `profile_classical.json`; REPORT.md §12 (it appeared while this review ran and was read at the end).

**Claim.** For each of the 81 bands (a_j, b_j] in the CSV, ζ(β + iγ) ≠ 0 whenever log γ ∈ (a_j, b_j] and β ≥ 1 − 1/(Z_j log γ). Here 4.614 ≤ Z_j ≤ 5.129.

**Versions reviewed** (md5): `cl_core.py` b345e4f0…, `check_cl.py` 41ef5bec…, `cert_classical.py` 43717f4b…, `profile_classical.json` a04bd23a…, `cl_constants.json` 26f5f4e0…, `zfr_classical_local.csv` 60bedcec…, `cert_classical_summary.json` 468de810…, `polyq.py` 6aa782f8… (identical to the audit's copy).

No file outside `review_classical/` was modified. Every script here is run as `python -I <script>.py` from this folder.

## Verdict

**No fatal issue. No major issue.**

- **The logic holds.** I re-derived the argument from the BTY LaTeX source and the audit. This covers the induction in s, the window, the inequality chain (CL), the five changes (a)–(e), and the η-monotonicity with μ held fixed. Every lemma is used inside its hypotheses. Every hypothesis the code does not assert was re-checked over all 15 655 cells (§5).
- **Independent numerics agree.** I wrote an mpmath implementation from the mathematics, not from `cl_core`:
  - L14 by direct quadrature of F from its definition;
  - W in closed form;
  - C_UP, P_ERR, Q_ERR, J and C_m recomputed.

  It reproduces the code's constants, either exactly or with the code on the safe side. At 14 test heights it gives a positive margin that is at least the code's cell margin (§6). A dense point scan finds no non-positive margin (§6.3).
- **Re-run.** A copy of the scripts re-run in `rerun/` reproduces `check_cl_output.txt`, `cl_constants.json`, the CSV and the summary byte for byte (timing line excepted).

COSMETIC findings (none affects the result):

| # | Where | Finding | Effect |
|---|---|---|---|
| C1 | CSV edges vs certified cells | The cells use binary floats for the band edges. The CSV prints decimals. At 13 edges (28.9, 29.2, 29.4, 29.7, 29.9, 30.2, 30.4, 30.7, 30.9, 31.2, 31.4, 31.7, 31.9) float(b_j) < b_j, by 7.1·10⁻¹⁶ or 1.42·10⁻¹⁵, and Z_{j+1} > Z_j. On (float(b_j), b_j] the CSV claims Z_j, but the certificate covers it only by band j+1's cells, i.e. with the weaker Z_{j+1}. Where float(b) > b the overlap goes the harmless way, since Z increases there. | A literal gap of measure 10⁻¹⁴ in log t. The margin at the top cell is ≥ 6.6·10⁻⁶ and its v-slope is about −3·10⁻³, so the claim is true there, but it is not certified. **Fix:** make the band edges exact decimal arb balls (`arb('28.9')`), or let each band's top cell reach b_j + 10⁻¹². |
| C2 | `check_cl.py`, Lemma 6, `B29` | The term 1/((2H)²T₀) is used for ∫_{T₀}^∞ dx/(x(2H+x)²). That is not an upper bound: the true value is 1.47·10⁻²⁵, against 2.8·10⁻³⁶. | None. B29 is dominated by 1/(2T₀²) = 5·10⁻²¹, and the k ≠ 0 far-zero bound stays 1.6·10⁻¹⁰ < 10⁻⁸. |
| C3 | `check_cl.py`, Lemma 12, `err36` | The first term is coded as (1/(2x_hi))·x_hi/y² = 1/(2y²). It should be x_hi/(2y²) ≤ 2.25/y². | None: 10⁻²⁴ against 1/(12y) = 5.6·10⁻¹⁴ < 10⁻¹⁰. |
| C4 | `check_cl.py`, `dQ/deta` | The code gives no justification for the bound 48.55. A correct justification exists, and REPORT §12.3 states it: at fixed μ each W-argument is c/η + const, so ∂W/∂η = −W′(z)·c/η², and \|W′(z)\| = ∫u e^{−zu}w ≤ w(0)/z² because 0 ≤ w ≤ w(0). The arguments satisfy X ≥ c(1 − 3η₀). | None. The true derivative is ≈ 4.1 (§4(e), §6.1), far below 135. |
| C5 | `G_of_mu`, `W_quad` | `acb.integral` is called with a ball endpoint D_SUPP. Whether it encloses the endpoint uncertainty is unverified. | None: the integrand vanishes to third order at d, so the effect is < 10⁻¹⁰⁰. |
| C6 | `cell_margin` | The cap y ≤ A/vb is redundant, since the band's own window candidate A/min(b_i, log T) ≤ A/vb already. It is harmless. In fact μ ≤ 0.9551 in every cell. | — |

Slack left on the table (not errors):
- the k = 0 digamma monotone bound loses 0.0067 in C_UP, i.e. ≈ 2.9·10⁻⁴ in Q;
- J is an upper sum, 23.651 against 23.642;
- Ford's C_m = 52.10 against the true sup |ξ³W₀| = |w″(0)| = 50.07 (§6.1);
- the G grid loses up to ≈ 3·10⁻⁵.

## 1. Induction (step 1)

**Statement.** H(s): no zero with log γ in any band j and β ≥ 1 − sA_j/log γ, for all bands simultaneously.

**Base case.** H(½) holds because ½A_j ≤ ½/4.58 = 0.1092 < 1/5.558691 = 0.1799. So the H(½)-region lies inside MTY's region.
- I checked MTY's statement in `proof/input_verification/sources_zfr/mty_rnt.txt`, Thm 1.3: no zeros for |t| ≥ 2 and σ ≥ 1 − 1/(5.558691 log|t|).

**Step: H(s) ⇒ H(s+ε) for s ∈ [½, 1).**
- A zero that violates H(s+ε) but not H(s) has η = 1 − β₀ ∈ (sA/v, (s+ε)A/v]. This is correct: H(s) gives β < 1 − sA/v, hence η > sA/v.
- Then η ≤ (1+ε)A/v ≤ (1+2ε)A_MAX/log H = η₀, since v ≥ log H for a genuine zero.
- After ⌈½/ε⌉ steps s ≥ 1, and H(1) is the claim. Every step starts from some s < 1.

**t ≥ H.** Cells with va < log H, i.e. the first cell, starting at 28.7296 < log H = 28.7296334, are harmless:
- for t < H, β₀ = ½ and η = ½ ≫ η_max, so there is no violating zero;
- the cell's v-ball simply contains extra values.

**Multiplicity.** As in BTY's footnote 2, one copy of ρ₀ is isolated and any others stay in the sum.

**μ.** μ = sy/η with η ∈ (sA/v, (s+ε)A/v]. This gives μ ∈ [yv/((1+ε/s)A), yv/A) ⊂ [y·va(1 − 2ε)/A, y·vb/A], which is the code's `mu_lo`/`mu_hi`. μ is essentially independent of s; η alone carries the s-dependence.

**Verdict: correct.**

## 2. Window (step 2)

For the zero ρ₀ at height t, σ = 1 − sy must lie to the right of every zero with |γ| ≤ T = 16t + T₀. Its mirror image 1 − σ must lie to the left of every such zero.

| Zeros with \|γ\| ≤ T | Why 1 − σ ≤ β ≤ σ |
|---|---|
| \|γ\| < H | RH (Platt–Trudgian): β = ½ |
| log γ in band j, γ ≤ T | H(s): β < 1 − sA_j/log γ ≤ 1 − sA_j/min(b_j, log T) ≤ 1 − sy |
| log γ > 60 (only if log T > 60) | MTY: β < 1 − 1/(5.558691 log γ) ≤ 1 − y ≤ 1 − sy (s ≤ 1) |
| negative γ | conjugation |
| lower bound | ρ ↦ 1 − ρ̄ |

Specific points checked:
- **Zeros between H and the first band.** None: a₀ = 28.7296 < log H, and the bands are contiguous up to 60 (asserted in `run_certify`, re-checked).
- **Zeros in [t − T₀, t] and up to 16t.** All are inside |γ| ≤ T, so the window covers them.
- **Zeros with |γ| > T.** They satisfy |Im(s_k − ρ)| ≥ T₀ for every k ≤ 16, so Lemma 6 (22) applies to them. It needs Re z ∈ (σ−1, σ) ⊂ [−η, 2σ−1+η], i.e. μ ≤ 1, which holds.
- **Band edges.** (a_j, b_j] is used consistently. The window candidate A_j/min(b_j, log T) is valid because log γ ≤ b_j inside band j.
  - `window_y` takes log T as an upper bound and min(b_j, log T) as an upper bound, and rounds each candidate down. That is the right direction.
  - Bands with a_j ≥ log T cannot meet [H, T] and are dropped (with a 10⁻⁹ safety margin). That is correct.
  - The float-versus-decimal issue is C1.
- **Cap y ≤ A/vb.** A smaller y only moves σ to the right, so it is always allowed. It is in fact implied by the band's own candidate (C6).
- **σ ≥ σ₀** is not asserted in the code, but it follows. log T lies in some band j (or above 60), so y ≤ A_j/log T ≤ A_MAX/log(16H + T₀). I re-checked this over all 15 655 cells (`hyp_check.py`): min[(1 − y) − σ₀] = 1.0·10⁻⁴ > 0.
- **Using log T at the cell top** gives one y valid for every t in the cell, because a larger T means a minimum over a larger set. σ may be chosen per zero, so using the cell's y is legitimate.

**Verdict: correct.**

## 3. The inequality chain (step 3)

I re-derived (CL) from the BTY LaTeX (eqs. (44)–(47), Lemmas 6, 9, 10, 12, 13), reading f(0) as ηw(0) (audit I10):

0.1186·ηw(0) ≤ Σ_n Λ(n)n^{−σ}f(log n)P(t log n) = Σ_k a_k Re Σ_n Λ(n)n^{−s_k}f(log n)
 = Σ_k a_k[ηw(0)Σ_m κ_m(−½log π + ½Re ψ((s_k+δ_m)/2+1)) + Re F(s_k−1) − Re Σ_ρ F(s_k−ρ) + E_k].

Then:
- Lemma 12 bounds the first term by ηw(0)[(aκ/2) log t + C′];
- Lemma 13 bounds Σ_k a_k Re F(s_k−1) by a₀F(σ−1) + 10⁻¹⁰η;
- Lemma 6 gives −Σ_k a_k Re Σ_ρ F ≤ −a₁[F(σ−β₀) + F(σ−1+β₀)] + Σa_k·10⁻⁸;
- |Σ a_k E_k| ≤ Σ a_k|E_k|.

Since σ−β₀ = σ−1+η and σ−1+β₀ = σ−η, this is exactly L14 ≤ ηw(0)[KC′v + C_UP] + 10⁻¹⁰η + 10⁻⁷ + Err, with KC = aκw(0)/2.

**Signs.** All are correct:
- C_UP < 0 enters Q as −ηw(0)C_UP > 0;
- an upper bound on C_UP is the safe direction;
- Σa_k·10⁻⁸ = 4.52·10⁻⁸ < 10⁻⁷.

**Lemma 12, k ≥ 1.** Σ_m κ_m(−½log π + ½ log(kt/2)) = (κ/2)log(kt/2π). The error multiplies Σ|κ_m| (audit I12); the code does this.
- I computed the sum directly with mpmath at t = H, σ = σ₀. It differs from (κ/2)log(kt/2π) by at most 2·10⁻²⁶ over all k ≤ 16.

**Lemma 12, k = 0.** ψ is increasing. The code uses argument (m+3)/2 for κ_m > 0 and (σ₀(1+2m)−m)/2+1 for κ_m < 0; both are the safe direction.

**Lemma 13.** It needs Re z ≥ −1, i.e. μ ≤ 1, and |z| ≥ H/η₀ > 10¹⁰. Both hold.

**Lemma 6.** The near-zero part follows from the window and (21). The far-zero constants were re-checked for our η₀ (1.5·10⁻⁹ and 1.6·10⁻¹⁰); the slip in B29 is C2.

**Lemma 9 (Kadiri Prop. 2.1).**
- Hypotheses w′(0) = w(d) = w′(d) = w″(d) = 0 were re-checked in `check_cl`.
- G₂(z)/z² = W₀(z/η) holds since g′(0) = 0.
- The formula itself is a refereed input, not re-derived (as in the audit).

**Verdict: correct.**

## 4. The changes (a)–(e) (step 4)

### (a) Lemma 5 (21) with c₀ = 1. **Correct.**

With z_m = (dm + iy)/η, d = 2σ−1, and r = (2σ₀−1)/η₀ ≤ Re z_m:
- Re[b_m w(0)/z_m] = b_m w(0)η·dm/(d²m² + y²);
- |b_m W₀(z_m)| ≤ |b_m|Cη³/|dm+iy|³ ≤ |b_m|Cη³/(dm·(d²m²+y²)).

So Σ_{m≥1} Re b_m W(z_m) ≥ w(0)ηd Σ_m (b_m m − |b_m|·[Cη²/(w(0)d²)]/m)/(d²m² + y²) ≥ (w(0)η/d)·B̃(y/d).

This uses Cη²/(w(0)d²) ≤ η₀²C(r,r)/(w(0)(2σ₀−1)²) = 5.3426·10⁻⁴ < ε₀ = 11/20000. The scaling is exact because all δ_m share one d. BTY's split is not needed; with our σ₀ it would in fact be invalid, since 2σ₀−1 = 0.98614 < 151/153 = 0.98693.

Independent numbers:

| Quantity | Value |
|---|---|
| η₀²C(r,r)/((2σ₀−1)²w(0)) | 5.342595·10⁻⁴ (ours and code's) |
| min_Y B̃(Y)(1+Y²) over [0, 20] (step 10⁻³) and a log grid to 10⁸ | 9.97·10⁻⁴, attained at Y → ∞ |
| limit of Y²B̃(Y) | Σm b_m − ε₀Σ\|b_m\|/m = 9.97·10⁻⁴, with Σ m b_m = 1/859 |

So the exact Sturm certificate is consistent with the numbers.

**Direct test of (21) by the closed form of W.** I wrote W(z) = Σ ∫(α+βu)e^{(λ−z)u}, which agrees with quadrature to 10⁻²⁸. I then evaluated Re F(iy) + Re F(2σ−1−iy) itself, including the m = 0 term that Heath-Brown's Re W ≥ 0 disposes of. This used 1241 values of y ∈ [0, 10⁷] at 7 parameter pairs:
- (σ₀, η₀), (σ₀, η₀/2), (σ₀, 0.001);
- (0.9999, η₀), (0.99965, 0.0034);
- (1 − 0.006831, 0.007538) and (1 − 0.00294, 0.00326), the actual extremes in our cells.

| Test | Minimum |
|---|---|
| [·]·(1+(y/d)²)/(ηw(0)d), all 7 pairs | ≥ 1.16·10⁻³, always at the largest y, i.e. the asymptote Σ m b_m/d² |
| interior points of the strip (9 × 400 grid) | > 0 (2.0·10⁻⁴ after normalisation) |

### (b) Lemma 11 / Lemma 10 with U = 54, p ≤ 31. **Correct.**

- h(u) = w(η₀u)Σκ_m e^{−d_m u} − κw(0). Independently, h(0) = 0 and min over (0, 54] (step 0.01) = 0.0119 near 0; h(54) = 0.0997; h < 0 first at u ≈ 55.4. This is consistent with `check_cl`'s rigorous h ≥ 0.099 on [½, 54].
- The reduction w(ηu)S_σ(u) ≥ w(η₀u)S_low(u) needs w decreasing and ≥ 0, S_σ ≥ 0 (Lemma 3) and the sign-dependent d_m. All are in place.
- Lemma 10: every p^m with p ≤ 31, m ≤ 15 has log p^m ≤ 15 log 31 = 51.51 < 54.
- G_p(σ, x) = Σ_m p^{−mσ}P(mx) is decreasing in σ, so G_p(σ,x) ≥ G_p(1,x) ≥ m_p for every σ ≤ 1. No σ₀ is needed.
- The m_p are the audit's certified values (part 3; m₅ = 0.00735649). Spot grid minima of G_p(1,x) at p = 2, 3, 5, 31 are above them.
- Independently, Σ_{p≤31} log p·m_p = 0.2353197119 and κ× = 0.1186186673 > 0.1186.

### (c) Error terms per (k, m). **Correct.**

- **T₁, all k.** Re ξ = (σ+δ_m−½)/η ≥ x_m/η₀ with x_m = σ₀(1+2m)−m−½. Ford gives |W₀(ξ)| ≤ C_m η³/(x_m² + (kt−y)²)^{3/2}.
- **T₁, k = 0.** This gives (C_m/2π)η³J(x_m). The Re ψ in J is Re ψ(¼ + iy/2), the right argument.
- **T₁, k ≥ 1, |u| ≤ kt−2** (y = kt+u). Pairing ±u gives log(kt+u) + log(kt−u) ≤ 2 log kt and ∫₀^∞(x²+u²)^{−3/2}du = 1/x², hence 2 log(kt)/x_m².
  - This needs |Re ψ(¼+iy/2)| ≤ log y for y ≥ 2. Independently, min_{y∈[2,10¹⁰]}(log y − |Re ψ|) = 0.676 at y = 2.
- **T₁, k ≥ 1, rest.** I₁ + I₃ ≤ 2[(6+log 3)/(2Y²) + (2 log Y + 1)/(4Y²)], Y = H − 2. I re-derived this using 1 + |y| ≤ 3w and kt + w ≤ 3w.
- **T₂.** For k ≥ 1, |s_k + δ_m| ≥ kt ≥ H gives C·η³/H³. For k = 0, |s| ≥ sp_m.
- **Total.** Σ_k a_k|E_k| ≤ η³(Sc·Σa_k log k + a·Sc·log t + a₀·(k = 0 terms) + tiny), with Sc = Σ_m|κ_m|C_m/(πx_m²).
- **Ford's bound.** The audit checked it at 40 points. On the lines Re ξ = ν that matter (64.88, 128.58, 129.76, 130.67, 194.64) I computed sup_y|ξ³W₀(ξ)| with the closed form. It is 50.0697 = |w″(0)| in every case, the limit at |ξ| → ∞, against C(ν, ν) = 52.10, 51.04, 51.03, 51.02, 50.70. ξ³W₀ is bounded and analytic on the half-plane, so the boundary line suffices (Phragmén–Lindelöf).

| Constant | Code (`cl_constants.json`) | Independent (mpmath) | Direction |
|---|---|---|---|
| C_m, m = 0..6 | 52.10120, 50.69671, 50.44000, 50.33240, 50.27324, 50.23583, 50.21003 | identical (same formula, independent code) | upper ✓ |
| J(x_m), m = 0..6 | 23.65101, 1.516341, 0.4229298, 0.1957443, 0.1161654, 0.07911545, 0.05855329 | 23.64179, 1.515720, 0.4226628, 0.1955828, 0.1160530, 0.07903007, 0.05848416 (quadrature) | code ≥ exact ✓ |
| Q_ERR | 278.20033166674 | 278.2003317 | equal ✓ |
| P_ERR | 396.56333 | 396.47895 (k = 0: 273.3206; k ≥ 1 log k: 123.1584) | code ≥ exact ✓ (+0.084, from the J upper sum) |
| BTY-style (single x₀) Q | — | 907.66 | the per-m x_m gain is real |

### (d) L14 directly. **Correct.**

- The m = 0 part is a₁W(1−μ) − a₀W(−μ) = ∫e^{μu}(a₁e^{−u} − a₀)w = G(μ).
- G is increasing on [0.879, 1] (121 certified balls). The grid point g = j/10⁴ ≤ μ_lo is asserted rigorously (`g.upper() <= mu_low.lower()`).
- The other 19 arguments are ≥ 1/η − 3μ ≥ R_MIN at η ≤ η₀, μ ≤ 1. The Taylor remainder is correct: ∫e^{−zu}M₃u³/6 = M₃/z⁴, and the e^{−zd} tails are < 10⁻⁵⁰.
- `L14_rest` matches the formula term by term: a₁ on both F(σ−1+η) and F(σ−η), a₀ on F(σ−1), and the m = 0 second term a₁W((σ−η)/η).

Independent L14 is the quadrature of F from its definition, F(z) = ∫₀^d e^{−zx/η}w(x)Σκ_m e^{−(2σ−1)mx/η}dx. A second, separate route via Σκ_mW((z+δ_m)/η) with W by quadrature agrees with it to 12 digits at all 14 heights. Both lie inside cl_core's ball G(μ) + L14_rest(η, μ) at the same point (radius 0.08–6.6·10⁻⁶) at all 14 heights (§6).

### (e) Worst case η = η_max; μ as an independent variable. **Correct.**

At the true point, all bounds of the chain hold (σ_t ≥ σ₀, η_t ≤ η₀, t ≥ H, μ_t ≤ 1), so Q(η_t, μ_t, v_t) ≤ 0.

Q(·, μ_t, v_t) is an explicit function of η. On [η_t, η_max] all L14 arguments stay ≥ R_MIN (η ≤ η₀, μ_t ≤ 1), so it is well defined there. It is decreasing there, because ∂Q/∂η ≤ |∂L14/∂η| + w(0)|C_UP| + 10⁻¹⁰ − KC·v, with v ≥ log H for the true zero, and the −3η²(P+Qv) term only helps. Hence Q(η_max, μ_t, v_t) ≤ 0, and the cell check Q(η_max-ball, μ-ball, v-ball) > 0, whose balls contain this point, gives the contradiction.

Treating μ as independent is legitimate. It is a pure monotonicity argument at the fixed true μ_t: no hypothesis of a lemma is used at the virtual point (η_max, μ_t). Only the explicit formulas for L14 and the RHS are evaluated there.

**The bound |∂L14/∂η| ≤ 48.55.** At fixed μ the arguments are m/η + const or (m+1)/η + const; the dependence through σ = 1 − μη cancels. So |∂W/∂η| = |W′(z)|·c/η² ≤ w(0)c/X², using |W′(z)| ≤ w(0)/z² (0 ≤ w ≤ w(0)). The X ≥ c(1−3η₀) bounds hold for μ ≤ 1, so DL is rigorous (C4).

Independent finite differences of the direct quadrature give ∂L14/∂η = 4.160, 4.154, 4.079, 4.050 at (η, μ) = (η₀, 0.88), (η₀, 1), (0.0045, 0.95), (0.0033, 0.88). This is far below both 48.55 and KC log H − w(0)|C_UP| = 135.2. The dense scan also evaluates Q at s = ½, ¾, 0.9, 1 (η = sA/v) and finds it decreasing in s (§6.3).

## 5. Per cell and hypotheses (step 5)

- **Code against the mathematics.** `cell_margin` implements (CL) as stated, with one exception, C1. Every piece is in the right direction:
  - η-ball = (1+ε)A/v-ball;
  - the μ-ball has `mu_lo` rounded down and `mu_hi` rounded up;
  - G is a lower bound;
  - `L14_rest` is a ball;
  - the error term is subtracted as a ball;
  - the result is `.lower()`.
- **Cell cover.** The cells exactly tile [float(a_j), float(b_j)]: a + (b−a)·n/n == b for all 81 bands. No bisection occurred, and there are 15 655 cells, matching the summary.
- **Hypotheses not asserted in the code**, over all 15 655 cells (`hyp_check.py` → `hyp_check_output.txt`):

  | Hypothesis | Result |
  |---|---|
  | σ ≥ σ₀ | min slack 1.02·10⁻⁴ |
  | η_max ≤ η₀ | min slack 5.6·10⁻⁵, at the bottom cell |
  | μ ∈ [0.88, 1] | actual range [0.880031, 0.955093] |

  μ_lo is closest to 0.88 in bands (57, 60]. There the design is limited by MU_MIN, not by the margin, which is 5%. That is why those bands sit at Z ≈ 5.13: they are correct but weak.
- **Stored constants** (string rounding):
  - C_UP: `(upper + 1e-25).str(30)`, an upper bound;
  - P_ERR, Q_ERR: `×(1+1e-20)` at 30 digits; the rounding error of 10⁻²⁷ is far below the 4·10⁻¹⁸ increase, so both are upper bounds;
  - `arb(string)` is a ball containing the decimal.
- **Constants not read back.** η₀, σ₀, J and C_m in the JSON are informational. `cl_core` recomputes η₀ and σ₀ from Z_MIN (asserted equal).
- **Re-run.** `rerun/` holds copies of `cl_core.py`, `check_cl.py`, `polyq.py`, `cert_classical.py` and `profile_classical.json`. `check_cl` ran in 18 s with 0 failures; certify ran in 11 s with all 81 bands OK. All outputs are identical to the work folder's.
- **Profile.**
  - The CSV equals `profile_classical.json` (edges and Z strings).
  - Coverage is (28.7296, 60], contiguous, all rows "proved".
  - 4.614 ≤ Z_j ≤ 5.129 < 5.558691, and all Z_j ≥ Z_MIN = 4.58 (asserted in `certify_band` and re-checked).
  - Z decreases only at 57 → 58 → 59 (5.129, 5.126, 5.122). These edges are integers, hence exact floats, so C1 does not arise there.

## 6. Independent numerics

`indep_classical.py` → `indep_classical_output.txt` (mpmath, dps 30, 7 min). It was written from the BTY formulas: w is typed from Def. 1, a_k come from the c_k, and κ_m, Ford's C, the window and the margin are all recomputed. It imports `cl_core` only at the end, for the comparison column.

### 6.1 Constants

| Quantity | Ours (independent) | Code | Note |
|---|---|---|---|
| w(0) | 5.6727875988616 | 5.67278759886 | = sec²θ(θtanθ + 3θcotθ − 3) |
| w″(0) | −50.0697014947 | −50.069701 | |
| KC = aκw(0)/2 | 5.03905010405 | 5.03905010405 | |
| a₁, a | 865534/497079, 2919857/828465 | same | from c_k |
| η₀, σ₀ | 0.00759983979882, 0.993069086787 | same | |
| ε₀ test value | 5.342595·10⁻⁴ | 5.34259·10⁻⁴ | < 5.5·10⁻⁴ |
| κΣ_{p≤31} log p·m_p | 0.1186186673 | 0.11861867 | > 0.1186 |
| min h on (0, 54] | > 0 (0.0119 at u = 0.01); h(54) = 0.0997 | h ≥ 0.0992 on [½, 54] | |
| C_UP | −1.68706367259 | −1.687063672586 (stored upper) | k ≥ 1: −1.2393174; k = 0 bound: −0.3291463 (exact at σ: −0.33585) |
| C_m (m = 0) | 52.1011976 | 52.1011976 | true sup \|ξ³W₀\| = 50.0697 |
| J(x₀) | 23.6417948 | 23.6510149 (upper sum) | |
| Q_ERR | 278.2003317 | 278.2003317 | |
| P_ERR | 396.478949 | 396.563328 | |
| ∂L14/∂η | 4.05–4.16 (4 points) | bound 48.55 | needs < 135.2 |

### 6.2 Margin at 14 heights (s = 1, η = A/v, σ = 1 − y(v), μ = yv/A)

Window y(v) is my own: min over bands with a_j < log T of 1/(Z_j min(b_j, log T)), plus MTY if log T > 60, capped at A/v. The code column is `cell_margin([v, v+10⁻⁷])`.

| v | Z | y | μ | L14 (direct quadrature) | code G(μ)+rest, same point | −err | margin (ours) | margin (code cell) |
|---|---|---|---|---|---|---|---|---|
| 28.730 | 4.614 | 0.00682943 | 0.905311 | 1.02393465 | 1.02393 ± 6.6e-6 | −3.601e-3 | 4.075e-4 | 3.894e-4 |
| 29.000 | 4.617 | 0.00676850 | 0.906254 | 1.02375251 | 1.02375 ± 4.3e-6 | −3.526e-3 | 2.916e-4 | 2.676e-4 |
| 30.000 | 4.630 | 0.00654370 | 0.908919 | 1.02300205 | 1.02300 ± 3.6e-6 | −3.262e-3 | 2.929e-4 | 2.742e-4 |
| 31.500 | 4.647 | 0.00623724 | 0.913011 | 1.02204189 | 1.02204 ± 3.2e-6 | −2.920e-3 | 1.351e-4 | 1.180e-4 |
| 31.850 | 4.651 | 0.00617024 | 0.914024 | 1.02184698 | 1.02185 ± 4.7e-6 | −2.848e-3 | 1.713e-4 | 1.524e-4 |
| 31.899 | 4.651 | 0.00616152 | 0.914136 | 1.02181961 | 1.02182 ± 2.1e-6 | −2.839e-3 | 5.360e-5 | 3.305e-5 |
| 32.000 | 4.653 | 0.00614099 | 0.914370 | 1.02175187 | 1.02175 ± 3.1e-6 | −2.817e-3 | 2.422e-4 | 2.171e-4 |
| 35.000 | 4.683 | 0.00562324 | 0.921678 | 1.02022233 | 1.02022 ± 3.1e-6 | −2.301e-3 | 2.802e-4 | 2.545e-4 |
| 40.000 | 4.723 | 0.00493030 | 0.931431 | 1.01825117 | 1.018251 ± 6.3e-7 | −1.709e-3 | 2.829e-4 | 2.640e-4 |
| 45.000 | 4.754 | 0.00438837 | 0.938803 | 1.01674021 | 1.016740 ± 4.9e-7 | −1.319e-3 | 1.968e-4 | 1.821e-4 |
| 49.900 | 4.780 | 0.00395855 | 0.944201 | 1.01552352 | 1.015523 ± 6.9e-7 | −1.052e-3 | 4.002e-4 | 3.859e-4 |
| 54.500 | 4.835 | 0.00340424 | 0.897043 | 1.00738726 | 1.007387 ± 3.8e-7 | −8.503e-4 | 6.532e-4 | 6.333e-4 |
| 57.500 | 5.129 | 0.00298475 | 0.880254 | 1.00343605 | 1.003436 ± 1.2e-7 | −6.391e-4 | 5.279e-2 | 5.276e-2 |
| 59.990 | 5.122 | 0.00286633 | 0.880735 | 1.00295001 | 1.0029500 ± 7.9e-8 | −5.889e-4 | 4.970e-2 | 4.968e-2 |

- **L14.** Two independent quadrature routes agree to 12 digits. Both lie inside the code's ball G(μ) + `L14_rest`(η, μ) at the same point.
- **The error term** agrees with the code's `detail['err']` to within 4·10⁻⁸. That gap is exactly the 0.084·η³ coming from the P_ERR difference.
- **Margins.** The code's cell margin is always below my point margin, by 1.4–2.5·10⁻⁵, i.e. 1–2% of the margin. This is the expected loss from the G grid (G at j/10⁴ ≤ μ_lo, G′ ≈ 0.14) and from the W_big remainder balls.
- **The tightest band, (31.8, 31.9].** The code's worst cell is [31.898, 31.9] with margin 6.6·10⁻⁶. The point margin near its top is ≈ 5·10⁻⁵ (ours) / 3·10⁻⁵ (code at a 10⁻⁷ cell). The cell-width loss accounts for the rest: the μ-ball relative width is 6·10⁻⁵, and v-slope ≈ −2.85·10⁻³ per unit.

### 6.3 Dense point scan

`scan_classical.py` → `scan_classical_output.txt` (23 min). It uses only my own constants (`indep_constants.json`), the window and L14 by direct quadrature. The points are a 0.02 grid on (28.73, 60] plus, for every band, a_j + 10⁻⁹, b_j − 10⁻⁹ and b_j: **1799 points**.

- **No point has margin ≤ 0.**
- **The 5 smallest relative point margins** are all at band tops, as expected: Z is fixed within a band and the 13.5η linear term decreases with v.

  | v | Relative margin | Code's minrel for that band |
  |---|---|---|
  | 31.8 | 4.59·10⁻⁵ | 8.2·10⁻⁶ |
  | 31.9 | 4.73·10⁻⁵ | 6.1·10⁻⁶ |
  | 29.6 | 6.45·10⁻⁵ | 2.9·10⁻⁵ |
  | 35.75 | 7.11·10⁻⁵ | 3.6·10⁻⁵ |
  | 41.0 | 7.24·10⁻⁵ | 3.9·10⁻⁵ |

  The ranking agrees with `cert_classical_summary.json`. The code's cell values are lower by the cell-width loss of §6.2.
- **Monotonicity in s** (s = ½, ¾, 0.9, 1, i.e. η = sA/v, σ = 1 − sy):

  | v | Q(½) | Q(¾) | Q(0.9) | Q(1) |
  |---|---|---|---|---|
  | 28.75 | 0.498 | 0.250 | 0.100 | 3.5·10⁻⁴ |
  | 31.899 | 0.498 | 0.249 | 0.0999 | 5.4·10⁻⁵ |
  | 45 | 0.499 | 0.250 | 0.100 | 2.0·10⁻⁴ |
  | 59.9 | 0.520 | 0.285 | 0.144 | 0.0498 |

  Q is decreasing in s, so s = 1 (η = η_max) is the worst case, as claimed.
- **Bands (57, 60]** carry 5% margin. Their Z ≈ 5.13 is forced by the G-table floor μ ≥ 0.88, since μ = yvZ with y set by MTY. They are correct but conservative. Extending GTable below 0.88 would lower them.

## 7. REPORT.md §12 cross-check

I read §12 after finishing the review above. It matches the code and my derivations:
- the induction and window of §12.2;
- (CL) and the η-monotonicity justification of §12.3, which supplies C4's missing argument;
- the lemma table of §12.4, including the observation that BTY's c₀ = 151/153 split fails for our σ₀;
- the rounding directions of §12.5;
- the input list of §12.6 (MTY Thm 1.3 verified against `mty_rnt.txt`);
- the CSV sha256 `f8a41422…afa083`, which matches the file.

Two small points:
- §12.1 says "every band is covered by closed v-cells … for **all** t in the cell". That holds for float edges; see C1 for the 13 decimal slivers.
- §12.2 states the cap as y ≤ A/v; the code uses A/vb. Both are valid, and the cap is redundant anyway (C6).

## 8. Files in this folder

| File | Content |
|---|---|
| `REVIEW.md` | this report |
| `indep_classical.py` → `indep_classical_output.txt`, `indep_constants.json` | independent mpmath implementation: constants, Lemma 3/5/11/10/12 checks, Ford-bound sanity check, error constants, ∂L14/∂η, margins at 14 heights against `cl_core` |
| `scan_classical.py` → `scan_classical_output.txt` | dense independent point scan (1799 points) and the s-monotonicity check |
| `hyp_check.py` → `hyp_check_output.txt` | σ ≥ σ₀, η_max ≤ η₀ and μ range over all 15 655 cells |
| `rerun/` | copies of `cl_core.py`, `check_cl.py`, `polyq.py`, `cert_classical.py`, `profile_classical.json`, and the re-run outputs (`check_cl_output.txt`, `cl_constants.json`, `zfr_classical_local.csv`, `cert_classical_summary.json`, `cert_classical_log.txt`, `cert_run.txt`), all identical to the work folder's |
