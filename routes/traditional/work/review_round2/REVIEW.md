# Referee report, round 2: Lemma D, Lemma B-W, and the local classical zero-free region

**Reviewed:**
- `work/phase2_lemmas/REPORT.md`, "Round 2 addendum", with `lemmaD_mollifier.py`, `lemmaB_weyl.py`, `lemmaB_count.py` (`BTZ_used`), `improvements.py`, `certify_lemmaD_demo.py`, `explore/lemmaD_check.py` and `explore/jcheck.py`;
- `work/phase1_littlewood/` §12 (Theorem C), with `cl_core.py`, `cert_classical.py`, `check_cl_output.txt`, `cl_constants.json` and `zfr_classical_local.csv`;
- the sources `ref/bel_v2.txt` (Bellotti §3–4), `ref/thorner_zaman_2208.11123.txt` (Props 2.10–2.11) and the BTY LaTeX at `proof/zfr_audit/bty_4.896/source/`.

**Rules.** Nothing outside `work/review_round2/` was modified. Every Python run used `-B`, so no `__pycache__` was written elsewhere.

**Labels.** "The report says" marks claims made by the authors. "I verified" and "I infer" mark my own work.

## Verdicts

| # | Item | Verdict | Trust as input? |
|---|---|---|---|
| 1 | **Lemma D** (mollifier on Re s = ½ in c₁) | **CONFIRMED** | **Yes.** It is an own lemma whose inputs are elementary. Fix the documentation gaps listed below. |
| 2 | **Lemma B-W** (Weyl exponent in TZ's −J bound) | **CONFIRMED**, with one cosmetic rounding slip | **Yes**, assuming the quoted inputs (Rademacher's lemma, Hiary–Patel–Yang, Patel–Yang, the arcs J₁, J₂, J₄, J₅ from Thorner–Zaman). |
| 3 | **Local classical region**, Z₁ = 4.614 at the bottom (`zfr_classical_local.csv`) | **CONFIRMED** for the induction, the window, the use of MTY above 60, and the coupled worst case. Spot checks are positive. | **Yes**, with two interface caveats: Z is non-monotone at 58 and 59, and the float band-edge slip (first reviewer's C1) is still unfixed. |

**Most serious problem found.** None is mathematical. In order of importance:

- **(i) Reproducibility.** `phase2_lemmas/certify_lemmaD_demo.py` no longer runs: line 21 raises `AssertionError: src.count(old) == 1`.
  - Cause: `phase0_bellotti/belarb.py` was refactored at 16:30. `piece_v2` now contains Lemma D natively, so the runtime source patch no longer finds its target.
  - Check: with the native integration I reproduced the first rigorous row exactly (C ≤ 127.584).
- **(ii) D.2 has no written proof.** The bound Q(y) ≤ (12/π²)√y + 1.5 log y + 2.4 is stated in the addendum as "elementary".
  - The code relies on it for y > 10⁶.
  - I supply a proof of a sufficient replacement (§1c). The claim stands.
- **(iii) Rounding slip in `lemmaB_weyl.A_eta`.** `float(x.upper())` rounds to nearest, so A_η can come out one ulp below 0.618/(eη).
  - I observed this at log T = 28.73 and at log T = 40.
  - In the pipeline it is absorbed by the ×(1 + 10⁻⁹) inflation of cf. The function on its own is not strictly rigorous.

---

## 1. Lemma D

### (a) The object

**The paper states** (Bellotti Lemma 3.4 proof, `bel_v2.txt` l. 970–980):
- S(X) = Σ Ψ(n)Θ(n)n^{−ρ}e^{−n/X} = (1/2πi)∫ζ(s+ρ)M(s+ρ)Γ(s)X^s ds;
- M(s) = Σ_{v≤V} Σ_{w≤W} ψ_v θ_w [v,w]^{−s}, with **lcm**, not vw;
- ψ and θ are the Barban–Vehov weights (3.1), with U, V and with W respectively.

**I verified** that this is the right object. Ψ(n)Θ(n) = Σ_{[v,w]|n} ψ_vθ_w, so ΣΨΘn^{−s} = ζ(s)M(s).
- Numerically (`lemmaD_indep.py`, part 1), ζ(s)M(s) agrees with the truncated series at s = 2 and s = 1.5. The differences equal the expected truncation tails.
- Lemma D bounds exactly this M. In (3.11) Bellotti bounds the same quantity, by Σ[v,w]^{−1/2} ≤ Σ_{n≤VW} d²(n)n^{−1/2}.

### (b) The proof, step by step

**I re-derived** every step.

1. **Triangle inequality.** |M(½+it)| ≤ S_abs := Σ|ψ_v||θ_w|[v,w]^{−1/2}. The coefficients are real and the bound does not depend on t.
2. **Gcd decomposition.** [v,w]^{−1/2} = (vw)^{−1/2}(v,w)^{1/2}, and (v,w)^{1/2} = Σ_{δ|(v,w)} φ_{½}(δ) with φ_{½} = μ⋆N^{½}.
   - φ_{½} = Π_{p^k‖δ}(p^{k/2} − p^{(k−1)/2}) ≥ 0, so S_abs = Σ_δ φ_{½}(δ)A_δB_δ.
   - Here A_δ = Σ_{δ|v}|ψ_v|v^{−½} and B_δ = Σ_{δ|w}|θ_w|w^{−½}.
   - Only squarefree v and w occur, so only squarefree δ do.
3. **Integral representations.** These match (3.1) exactly, including the case v ≤ U.
   - |ψ_v| = μ²(v)·Δ^{−1}∫_U^V 1_{v≤y} dy/y, valid for U ≥ 1.
   - |θ_w| = μ²(w)·(log W)^{−1}∫_1^W 1_{w≤y} dy/y.
4. **Restricted sums.** Σ_{v≤y, δ|v} μ²(v)v^{−½} ≤ δ^{−½}Q(y/δ) ≤ c√y/δ. Dropping (m, δ) = 1 is fine because all terms are non-negative, and Q = 0 for y/δ < 1.
   - Integrating gives A_δ ≤ 2c(√V − √U)/(Δδ) and B_δ ≤ 2c(√W − 1)/(δ log W).
   - Numerically, the largest ratio of A_δ to its bound is 0.914, and of B_δ to its bound 0.900.
5. **The δ-sum.** Σ_δ μ²(δ)φ_{½}(δ)/δ² = Π_p(1 + (√p − 1)/p²) = Π_p(1 + p^{−3/2} − p^{−2}) = P*. Extending the sum to all δ is valid, since every term is ≥ 0.

### (c) The constants

**The supremum c.**
- Q is constant on [m, m+1) while √y increases, so sup_{y≥1}Q(y)/√y is a maximum over the integers. For y < 1, Q = 0.
- **I verified:**
  - the argmax over m ≤ 10⁶ is m = 7;
  - c = Q(7)/√7 ∈ [1.32963494892258 ± 5·10⁻²³] (an Arb ball);
  - the second-best value is 1.31893 (m = 3), a gap of 0.0107.

**D.2, the tail for y > 10⁶ (proof not written in the report).** D.2 itself holds numerically for every m ≤ 10⁶, with slack ≥ 2.6. A proof of a sufficient replacement:
- Q(y) = Σ_{d≤√y}(μ(d)/d)S(y/d²), with S(z) = Σ_{k≤z}k^{−½} = 2√z + e(z) and −2 < e(z) ≤ 0 for z ≥ 1.
- Hence Q(y) ≤ 2√y Σ_{d≤√y}μ(d)/d² + 2Σ_{d≤√y}1/d ≤ (12/π²)√y + 2√y/⌊√y⌋ + 2 + log y.
- For y ≥ 10⁶ this gives Q(y)/√y ≤ 12/π² + (4.002 + log y)/√y ≤ 1.2337 < c. The middle expression is decreasing in y.
- So c = Q(7)/√7 holds rigorously. This can replace D.2 in the write-up.

**P\*.**
- My float product over p ≤ 10⁷ is 1.47241. With the tail factor e^{2/√P} it is ≤ 1.47334.
- The code's certified bound 1.47523 uses P = 10⁶ and is valid.
- The value "1.4723" in the module docstring is a typo, not a bound.

**The full constant and the Arb code.**
- 4c²P* ≤ 10.4324 (code). My value is ≤ 10.419 with the sharper P*.
- `certify_c` checks every integer m ≤ 10⁶ in Arb. Its tail uses D.2 (see above).
- `certify_Pstar`'s tail Π_{p>P} ≤ exp(Σ_{n>P}n^{−3/2}) ≤ e^{2/√P} is correct.
- `KD_upper` drops the factors (1 − ·) ≤ 1 and uses log T at the bottom of the range, where K_D is decreasing in L. Both are safe.

### (d) The plug-in

**The paper's structure.** In (3.11) the factor d₂(VW)^{½}log⁴(VW) is a bound on sup_t|M(½+i(γ+t))|. It multiplies the whole integral ∫|ζ||Γ|. That integral is split into (3.12), (3.13) and (3.16).

**Phase 0's code.** In `piece_v2`, (VW)^{½}X^{½−α₀} sits in `base·L`, and the bracket is (2·I2c·T^{27/164} + E312 + E313). Replacing D2VW by K_D (= Mfac) in SU therefore replaces exactly sup_t|M| ≤ K_D(VW)^{½}. The triangle-inequality bound is uniform in t, as (3.11) requires.

**S1t.** The term |M(1)| in (3.10) keeps D2VW, which is conservative.

**Hypotheses.** Lemma D needs U = T^u ≥ 1 and W = T^w > 1. Both hold.

**Reproduction** (`rerun_lemD_row.py` → `rerun_lemD_row_output.txt`; Phase 0's native lemD integration):

| Row [log 3e12, 29], parameters (0.9927, 2.244, 3.625, 0.600, 4.836, λ = 18) | Result |
|---|---|
| lems = A, B-W, C, D | C ≤ **127.584**, B = 9.672, C·e^{B/4.62} = **1035.1** (as reported). c₁ = 0.9678, SU = 0.032, K_D = 0.01524 |
| same parameters without D | c₁ = −1.3·10⁷, i.e. infeasible: SU with D2VW = 6.4·10⁶ |

**I infer** that at the re-optimised parameters the gain is due entirely to Lemma D. The float comparison `explore/r2_combined_low.txt` (base 3644 against D 1074, ×0.295) uses lemmas A, B and C in both columns. The figure "×0.29 for Lemma D alone" is therefore correctly attributed.

**Other hypotheses at these parameters.**
- They violate u + v < x of (3.8). That condition is used only in Bellotti's d₄ (Lemma 4.2, l. 1450–1535), which Lemma A replaces.
- (4.9) is not needed with Lemma C(ii).
- Excluding these two from the hypothesis check is legitimate. I checked where (3.8) is used in `bel_v2.txt`.

### Brute force (`lemmaD_indep.py`, independent code)

| Check | Result |
|---|---|
| S_abs against the Lemma D bound, 11 cases (integer and non-integer U, V, W; U = 1; tiny Δ) | bound/S_abs = 1.41–2.64; the bound always holds |
| max_t |M(½+it)| on t ∈ [0, 200] | far below S_abs, e.g. 7.05 against 30.35 |

### Suggestion (free gain, not checked in code)

Bellotti's c₅ uses G(s) = Σθ_jθ_k[j,k]^{−s}. This is M with U = 1 and V = W.
- Phase 0 replaced Bellotti's invalid |G(½+it)| ≤ W|G(1)| by 16·P_h·W/log²W, with P_h = P* (the same diagonalisation, with Σ log(Y/m)m^{−½} ≤ 4√Y).
- Lemma D with U = 1 gives 4c²P*(√W − 1)²/log²W, i.e. 16 → 7.07, or c₅ ×0.44.

---

## 2. Lemma B-W

**The paper states** (TZ, proof of Prop 2.11; `thorner_zaman_2208.11123.txt` l. 430–550):
- −Re ζ′/ζ(s) = Re 2/(s²−1) − Σ_{|s−ρ|<r₁}Re(1/(s−ρ) − (s−ρ)/r₁²) − J (Heath-Brown Lemma 3.2, with F = ((z−1)/(z+1))ζ);
- J is split as J₁ + … + J₅;
- J₃ (θ ∈ [π/2, 3π/2]) is bounded by Phragmén–Lindelöf between σ = ½, where Prop 2.10 gives |F| ≤ e^{¼log|1+it| + 1.0908}, and σ = 1 + r, where |F| ≤ 1 + 1/r.

**I verified the following.**

**Boundary bound on σ = ½.** |F(½+iy)| ≤ |ζ(½+iy)|, since |(z−1)/(z+1)| ≤ 1 for Re z ≥ 0.
- |y| ≤ 3: 1.461 (Arb in the code; my grid maximum is 1.46036).
- 3 ≤ |y| ≤ e¹⁰⁵: HPY 0.618|y|^{1/6}log|y| ≤ (0.618/(eη))|y|^{1/6+η}, using log y ≤ y^η/(eη), which holds for all y > 0.
- |y| ≥ e¹⁰⁵: Patel–Yang 66.7|y|^{27/164} ≤ A_η|y|^{1/6+η} if A_η e^{105(2/984+η)} ≥ 66.7.
  - With A_η = 0.618/(eη), the minimum over η > 0 of that expression is 80.3 (at η = 1/105). So the side condition always holds.
  - Remark: HPY's bound is in fact valid for all |t| ≥ 3, and Bellotti's Lemma 2.5 just splits the ranges. The PY branch is unnecessary but harmless.
- Finally |y| ≤ |1+iy|, so |F(½+iy)| ≤ A_η|Q + ½ + iy|^{1/6+η} with Q = ½ on the whole line.

**Rademacher's lemma** (standard form: a < b, Q + a > 0, α ≥ β, growth ≤ C·exp(e^{k|t|}) with k < π/(b−a)). Its hypotheses hold:
- a = ½, b = 1 + r, Q = ½;
- α = 1/6 + η ≥ β = 0;
- F is regular in the strip (the pole at 1 is cancelled, and −1 lies outside) and polynomially bounded;
- B = 1 + 1/r on σ = 1 + r.

This is exactly how TZ themselves apply the lemma, with α = ¼. The UNSURE in the report concerns only the exact wording of Rademacher's statement. I share that small reservation, but the version used is the standard one.

**Arc integration.** On the arc σ = 1 + r + r₁cos θ the PL exponents are −2r₁cos θ/(1+2r) and (1 + 2r + 2r₁cos θ)/(1+2r), both in [0, 1] for r₁ ≤ ½ + r.
- log|½ + σ + iy| ≤ log(√2T) = ℓ, since |y| ≤ T + 1 and σ < 3/2. The coefficient is ≥ 0.
- (1/(πr₁))∫|cos θ|·[…]dθ → X/(1+2r) + (4/π−1)log(1+1/r)/(1+2r), with X = (1/6 + η)ℓ + log A_η.
- Numerical check (`lemmaBW_indep.py` (a)): the r₁ → (½+r)⁻ limit matches the closed form to 10⁻⁸ at r₁ = ½ + r − 10⁻⁶.
- Only an upper bound for log|F| is needed for −J₃, so TZ's positivity remark is not needed.

**"J₁ + J₂ + J₄ + J₅ ≤ 2.6908 unchanged": correct.** Strictly, the needed statement is −(J₁+J₂+J₄+J₅) ≤ 2.6908.
- TZ's bound for those arcs uses only Re(s + r₁e^{iθ}) ≥ 1 + r, together with the lower bound for |ζ| and |(z−1)/(z+1)| there.
- It never uses the half-line bound.

**Use in `lemmaB_count`.**
- `BTZ_used = min(BTZ, BTZW)`, and both are valid.
- BTZW is decreasing in r and increasing in log T, which justifies evaluating at (r_lo, L_b).
- The k-terms use log(kT), which is consistent.

**Cosmetic issue.** `A_eta` computes `arb(max(1.461, float(x.upper())))`, and float() rounds to nearest. I measured A_η − 0.618/(eη) = −5.6·10⁻¹⁷ at log T = 28.73 and −9·10⁻¹⁸ at log T = 40.
- The effect on BTZW is about 10⁻¹⁷. It is covered by the `cfB = cf·(1 + 10⁻⁹)` inflation in every driver I saw.
- **Fix:** use `math.nextafter(..., inf)`, or keep the value as an arb.

**Sanity check (float).** At t = 2000 and 10⁴ with r = 0.05, −J = −0.41 and −0.40, against BTZW = 6.10 and 6.51.

---

## 3. The local classical zero-free region (Phase 1c, Theorem C)

**Documentation.** It is sufficient to review: REPORT §12, the code, and the first classical review `phase1_littlewood/review_classical/REVIEW.md`. I formed my own view first and read that review afterwards.

### Induction

**Base case.**
- H(½) is implied by MTY (Thm 1.3, |t| ≥ 2), because ½A_j ≤ 1/(2·4.58) < 1/5.558691.
- Z_MIN = 4.58 ≤ Z_j ≤ Z_MTY is asserted.

**Step: H(s) ⇒ H(s+ε), simultaneously for all bands.**
- A zero violating H(s+ε) but not H(s) has η ∈ (sA/v, (s+ε)A/v].
- The step for band i uses only level s for every other band, so it is **not circular**.
- ⌈½/ε⌉ steps reach s = 1.

**Window: every zero with |γ| ≤ T = 16t + T₀ satisfies 1 − σ ≤ β ≤ σ, where σ = 1 − sy.**

| Zeros | Reason |
|---|---|
| \|γ\| < H | RH (Platt–Trudgian); the first edge 28.7296 is < log H |
| log γ in band j, \|γ\| ≤ T | H(s) with y ≤ A_j/min(b_j, log T) |
| log γ > 60 | MTY with y ≤ 1/(5.558691 log T) and s ≤ 1 |
| lower bound on β | the symmetry ρ ↦ 1 − ρ̄ |

- **Bands above the current band.** Using them is legitimate: they are part of the same simultaneous hypothesis H(s).
- **MTY above the profile.** Using it is legitimate: it is a refereed, unconditional input.
- **Why K = 16.** BTY's K = 16 is the degree of P (I checked this in BTY §4). So |γ| > Kt + T₀ gives |Im(s_k − ρ)| ≥ T₀ for all k ≤ K, which is what Lemma 6/(22) needs.
- **Consequences:** μ ≤ 1 and σ ≥ σ₀.

**Coupled worst case.** μ = sy/η lies in [yv/((1+ε/s)A), yv/A] for every s, and η alone carries the s-dependence.
- At fixed μ, the m = 0 part G(μ) does not depend on η.
- ∂Q/∂η ≤ |∂L14/∂η| + w(0)|C_UP| − KC·log H < 0, using |W′(z)| ≤ w(0)/z², which needs 0 ≤ w ≤ w(0) and is certified in `check_cl`.
- Hence η_max = (1+ε)A/v is the worst case. Treating μ as a free variable over a superset box is valid.
- **I verified numerically** that Q is strictly decreasing in η on [A/(2v), A/v] at v = 28.75 (`classical_spot.py`).

### Independent spot check (`classical_spot.py`, mpmath)

This code does not import `cl_core`.
- **Built from BTY's LaTeX:** w, κ_m, a_k (all a_k ≥ 0 ✓) and F as defined there; L14 by direct quadrature; the window from the CSV profile.
- **Taken from `cl_constants.json`:** C_UP, P_ERR and Q_ERR, as recomputed by the first reviewer.

| Result | Value |
|---|---|
| Points checked | 27 (endpoints and middles of 9 bands: 28.73–28.8, 29.1–29.2, 29.4–29.5, 31.7–31.9, 37.5–38, 45–46, 55–57) |
| Relative margin Q/(KC·A) | positive at every point, 4.6·10⁻⁵ to 1.3·10⁻³; the smallest is at the tops of 31.7–31.9, consistent with the certified cell minimum 6.1·10⁻⁶ |
| Window at the bottom | y·log T = 0.2152, μ = 0.9053 |
| Sensitivity | with a uniform Z in the window the bottom would allow Z ≈ 4.608; the rising profile costs 0.006, giving 4.614 |

### Caveats (not errors in Theorem C)

1. **First reviewer's C1 is still open.** The band edges are binary floats, e.g. float(28.9) < 28.9.
   - On a set of measure about 10⁻¹⁵ in log t, the CSV's Z_j is certified only through band j+1's weaker Z_{j+1}.
   - Fix: use decimal arb edges.
2. **Z is non-monotone at 58 and 59** (5.129 → 5.126 → 5.122), so the classical width 1/(Z log t) jumps *up* there.
   - Bellotti-type consumers need 1 − β ≥ ν(T) for all γ ≤ T, so they must use the running minimum, or replace bands 57–60 by a monotone envelope.
   - Phase 0's `check_hypotheses` does test monotonicity of the combined widths. **I infer** the combined (max) width is probably monotone there anyway, but this was not checked.
   - The report itself calls bands > 54 "of no use".
3. **Inputs I did not re-derive.** These are BTY's Lemma 9 (Kadiri's explicit formula), the m_p table, and the error-constant derivations.
   - The first reviewer re-derived the error constants independently.
   - Tier: the BTY *method* comes from a preprint, re-checked; the inputs are refereed.

---

## Files (all in `work/review_round2/`)

| File | What it does | Re-run |
|---|---|---|
| `lemmaD_indep.py` → `lemmaD_indep_output.txt` | Lemma D: object identity, S_abs against the bound, A_δ/B_δ, c (argmax and Arb ball, D.2, own tail bound), P* | `python -B lemmaD_indep.py` (30 s) |
| `rerun_lemD_row.py` → `rerun_lemD_row_output.txt` | first rigorous row with Phase 0's native lemD, with and without D | `python -B rerun_lemD_row.py` (30 s) |
| `lemmaBW_indep.py` → `lemmaBW_indep_output.txt` | arc limit, boundary-bound ranges, PY side condition, A_η rounding, −J sanity | `python -B lemmaBW_indep.py` (1–2 min) |
| `classical_spot.py` → `classical_spot_output.txt` | independent (CL) margins at 27 points, η-monotonicity, sensitivity | `python -B classical_spot.py` (about 5 min) |
| `demo_rerun_output.txt` | the AssertionError from `certify_lemmaD_demo.py` | — |

The scripts use floats and mpmath for exploration only. The only rigorous objects here are the Arb ball for c = Q(7)/√7 and Phase 0's Arb row bound.
