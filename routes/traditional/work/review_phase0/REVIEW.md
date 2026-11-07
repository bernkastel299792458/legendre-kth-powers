# Referee review of Phase 0 (Bellotti log-free zero-density audit)

Reviewer: independent referee sub-agent, 2026-11-06. Scope: `work/phase0_bellotti/REPORT.md`, its code and CSVs, against `work/ref/bel_v2.txt` (arXiv:2405.12545v2), `work/ref/bellotti_constants.py.txt`, `work/ref/thorner_zaman_2208.11123.txt` (TZ) and `work/ref/ramare_zuniga_alterman_2405.12662.txt` (RZA).
Nothing outside `work/review_phase0/` was modified.

## 0. Verdicts

| # | Item | Verdict |
|---|------|---------|
| 1 | Counting gap in §4 is real; multiplicities ≤ 3 within δ, ≤ 2 per side per band; the "2" in (4.6)/(4.7) is not a two-sides factor | **CONFIRMED** |
| 2 | Sharp fix (Hn, P_j, J₁, A = Ycoef·d₄d₅Hn/w) is a valid upper bound for **every** configuration | **CONFIRMED** (re-derived independently; code matches) |
| 3 | λ-box modification (box height λδ) | **CONFIRMED.** ñ does scale with λ and the code does scale it. The gain is real, not spurious. One cosmetic hypothesis issue at the box edges, fixable in one line (§3.4). |
| 4a | \|G(½+it)\| ≤ 16·P_h·W/log²W, P_h ≤ 1.48111 (her W·\|G(1)\| invalid) | **CONFIRMED** (P_h ≤ 1.478591 by my computation) |
| 4b | d₃ code slip (factor log²T) | **CONFIRMED** (moot: d₃ is no longer used) |
| 4c | Lemma 3.2 flawed; d₄ ≤ T^{u−x} + F(τ)·x/(v−u) from RZA Cor 1.2 | **CONFIRMED** (flaw and replacement both checked) |
| 4d | (3.10): (u+w)⁴ should be (v+w)⁴ | **CONFIRMED** |
| 4e | Lemma 2.7 (uses d₁(X) for u < X, d₁ decreasing; code permutes arguments) | **CONFIRMED**; the replacement bound is correct |
| 4f | Monotonicity in (4.9) needs x > Z/2; factor K = e^{κ−1}/κ | **CONFIRMED** (K re-derived) |
| 5 | Independent Arb evaluation of C | **CONFIRMED.** All 1596 rows of rows_reopt.csv satisfy C_csv ≥ my rigorous bound and all hypotheses (details in §5). |
| 6 | Conventions, ranges, zero-free inputs, low zeros | **No error found.** Ford-region validity and the RZA published version are UNSURE (both inherited, not checked here). The b₁/b₂ decoupling is loose (an improvement opportunity, §6.4). |

**Most serious problem found.** Nothing that invalidates a row. The closest thing to a gap is in the λ-box ñ step (REPORT §5, `belarb.b12`): it applies TZ Prop 2.11, which assumes 3·10¹² ≤ |t| ≤ T for the disc centre, to boxes whose centre can lie up to λδ/2 ≈ 0.13 above T or below 3·10¹². This is not addressed in REPORT.md. The fix is one sentence (§3.4) and changes no number.

**Can rows_reopt.csv be trusted as an input?** Yes, at the tier "refereed inputs (or + audited preprint BTY 4.896) **+ our own repair of Bellotti §4 + our own λ-box lemma + our own small improvements**". Every claimed C is ≥ an independently computed rigorous bound; the margin is 1.1–34%. Its status column records only the input tier, so any write-up must state the "own lemma" tier explicitly. The λ-box argument and the counting repair should be written out as a self-contained lemma with proof; §§2–3 below can serve as the draft.

---

## 1. The counting gap (§4 of Bellotti)

**The paper says.**
- (4.1): boxes α ≤ σ ≤ 1, (n−1)δ ≤ t ≤ nδ with δ = 1−α, and one representative chosen arbitrarily per box.
- Before (4.9): "for every fixed γ_r there is a unique representative zero with imaginary part γ_s such that |γ_r−γ_s| < δ".
- Before (4.11), and again before (4.13): "for each n … there is a unique representative zero … such that nδ ≤ |γ_r−γ_s| ≤ (n+1)δ".
- (4.6): |X^z − (U/L²)^z| ≤ 2X^{Re z} gives the prefactor 2|G(1)|X^{2−2α}.

**I infer.**
- Let γ_r = (m−1+θ)δ in box m, with θ ∈ [0,1]. A representative in box m+k (k ≥ 1) satisfies γ_s−γ_r ∈ [(k−θ)δ, (k+1−θ)δ]. One in box m−k satisfies γ_r−γ_s ∈ [(k−1+θ)δ, (k+θ)δ].
- **Within distance < δ:** r itself, plus the representatives of boxes m±1. So up to 3. Phase 0's 0.99δ/1.01δ example is valid.
- **Per band [nδ, (n+1)δ] on one side:** boxes m+n and m+n+1 can both land in it (the intervals have length 2δ). So up to 2 per side, 4 in total.
- **The factor 2.** (4.9) reads J·1.0067·d₅/w·X^{2−2α}/(δ log T). This equals 2·(d₅/(w log T))·X^{2−2α}·1.0067/(2δ)·J, so the 2 of (4.6) is used up against the 1/(2δ). In (4.11) the 2 is the same prefactor of (4.7) again. Neither is a factor for the two sides.
- **Worst case.** The adversarial worst case with λ = 1 is about 2H_N + 1 per representative, against her H_N + ½. So her c₂+c₃ is too small by a factor of about 2 (Phase 0 measures 1.94–2.20 on C).

The "minimal fix" (c₂' = 3Kc₂, c₃' = 2c₃) is not used in any CSV; every CSV uses the sharp fix (`count='fixed'` in both OPT_CORR and OPT_IMPR). My rough count suggests c₃' = 2c₃ is adequate only because of the slack in her 1.12. UNSURE, and irrelevant to the rows.

## 2. The sharp fix: my own derivation

**Per-pair bound.** Let z = 2−ρ_r−ρ̄_s, a = Re z = 2−β_r−β_s ∈ [2ν(T), 2δ] (β ≥ α for representatives; β ≤ 1−ν(γ) ≤ 1−ν(T) because the widths are non-increasing), and b = γ_r−γ_s.
- |Γ(z)| = |Γ(1+z)|/|z| ≤ Γ(1+a)/|z| ≤ g/|z| with g = 1 (since 0 ≤ a ≤ 1). Also |z| ≥ max(a, |b|).
- |X^z − Y^z| ≤ X^a(1 + (Y/X)^a) ≤ X^a(1 + (Y/X)^{2ν}), with Y = U/L² < X. This is the Ycoef.
- f(a) = X^a/a is decreasing then increasing (minimum at a = 1/log X), so sup_{[2ν, 2δ]} f ≤ max(f(2ν), f(2δ)) ≤ K·f(2δ). Here K = 1 if κ := 2ν log X ≥ 1, and otherwise K = e^{κ−1}/κ, using t e^{−t} ≤ e^{−1} with t = 2δ log X.
- Hence |residue term| ≤ |G(1)|·Ycoef·X^{2δ}·min(K/(2δ), 1/|b|) for every pair. For |b| ≥ 1 one may instead use |Γ(z)| ≤ S(|b|) := √(2π)|b|^{3/2−2α₀}e^{−π|b|/2+1/(6|b|)}, from Olver/Stirling with Re z > 0, a − ½ ≤ 3/2 − 2α₀ and |b| ≥ 1. S is decreasing on [1, ∞).

**Per-representative sum** (in box units d = |b|/(λδ), with m(d) = min(K/2, 1/(λd))):
- s = r contributes K/2.
- Box m±j contributes at most m(j−θ) + m(j−1+θ), since m is decreasing.
  - j = 1 with d* := 2/(Kλ) ≤ ½: the exact sup over θ is K/2 + 1/(λ(1−d*)). I checked both pieces, [0, d*] (increasing) and [d*, ½] (convex, endpoint values), and that 1/d + 1/(1−d) ≥ 4.
  - j−1 ≥ d*: the function is convex in θ on [j−1, j], so the sup sits at an endpoint: m(j−1) + m(j).
  - Otherwise: one of the two distances is ≥ j−½ (they sum to 2j−1), so the pair is ≤ m(j−1) + m(j−½).
- **Tail.** For j ≥ J₁+1, with J₁ ≥ 1/(λν), the distance is ≥ (j−1)λδ ≥ J₁λν ≥ 1. On each side the lower bounds (j−1)λδ are spaced exactly λδ apart, so Σ S ≤ S(1) + (λδ)^{−1}∫₁^∞S. Multiplied by δ, both sides give 2δS(1) + (2/λ)∫₁^∞S.
- Summing Σ_j sup_θ is ≥ sup_θ Σ_j, so this is an upper bound for every configuration, not just the sampled ones.

**Assembly.**
- (Σ_r|a_r|)² ≤ d₄·Σ_{r,s}|…| (Cauchy–Schwarz as in (4.3), checked), so J²c₁² ≤ J·Ycoef·d₄·(d₅/(wL))·X^{2δ}Hn/δ + J²c₅. Therefore J ≤ A·X^{2δ}/(δL(c₁²−c₅)) with **A = Ycoef·d₄d₅Hn/w**. This is exactly `belarb.piece`.
- The code takes J₁ = ⌊1/(λν_lo)⌋ + 2 (REPORT: ⌈·⌉); this is conservative.

**Float adversarial check** (`adversarial_Hn.py`). r sits at θ, and every other representative is pushed to the end of its box nearest r, which is the extremal configuration. θ is scanned and far pairs are included.
- Grid: α₀ ∈ {0.9927, 0.985, 0.98}, Z ∈ {5.558691, 4.896}, L ∈ {28.8, 50, 80, 100}, λ ∈ {1, 4, 9.7, 11, 13.3}, three values of δ.
- Result: max(exact/Hn) = 0.99906 < 1. The bound is tight at λ = 1 (0.996–0.999) and looser for larger λ.

## 3. The λ-box modification (the consequential claim)

### 3.1 Every place where box height enters Bellotti's argument
1. **(4.1) the box itself.** Height λδ, width δ. It lies in the closed disc centred at 1+it_c with radius ρδ, where ρ = √(1+λ²/4). ✓
2. **Zeros per box, ñ (Lemma 2.4 / Cor 2.3 / TZ Prop 2.11).** TZ needs 0 < r < ½ and 3·10¹² ≤ |t| ≤ T. In the rows r₀ = ρ(1−α₀) ≤ 0.11 < ½ (checked for all rows). Each zero in the disc has Re 1/(1+r+it−ρ) ≥ 1/(2r), which gives n ≤ 2r·(Prop 2.11 RHS). ✓ ñ **must grow with λ**, and it does in the code (§3.2). For the |t| hypothesis see §3.4.
3. **|γ_r−γ_s| < δ case.** No longer special: min(K/2, 1/(λd)) handles every distance. ✓
4. **Band counting (4.11)/(4.13).** Replaced by the per-box P_j and the tail in units of λδ. ✓
5. **J versus N(σ,T).** Every counted zero (β ≥ σ = α, 3·10¹² < γ ≤ T) lies in some box; such a box has a representative with β ≥ α; each box contains ≤ ñ zeros. So N ≤ J·ñ. ✓
6. **(4.22)–(4.23).** N ≤ J·ñ ≤ [A/(c₁²−c₅)]·X^{2δ}·ñ(δ)/(δL), and ñ/(δL) ≤ b₁ + b₂/(δL) ≤ b₁ + b₂Z, using δ ≥ ν (for σ > 1−ν(T), N = 0). C = A(b₁+b₂Z)/(c₁²−c₅) is exactly `Cv` in the code. ✓
7. **c₁ (Lemma 3.4) and c₅ (4.15)–(4.21).** These do not involve the boxes: c₁ is per representative, and c₅ bounds every one of the J² pairs uniformly. ✓
8. **K and Ycoef.** These depend only on a ∈ [2ν, 2δ], not on the boxes. ✓

### 3.2 What the code uses for b₁, b₂ when λ ≠ 1
`belarb.b12`, branch `exact`:
- r₀ = ρ(1−α₀) and b₁ = ρ·max(½, 1/(2(1+2r₀)) + 32r₀²/(1+2r₀)²).
- b₂ = 2r₀·4.7908/(4+8r₀) + 2r₀(4/π−1)log(1+1/r₀) + 5.3816r₀ + 16r₀²(4−r₀)/(1+2r₀)² + 2.

**My check of these formulas.**
- Expanding 2r·[Prop 2.11 RHS] with r = ρδ, the coefficient of δL is ρ·f(r), where f(r) = 1/(2(1+2r)) + 32r²/(1+2r)².
- f′ ∝ 62r − 1, so f is quasi-convex and its max on (0, r₀] is at an endpoint. ✓
- The constant terms are increasing in r (checked by derivative), so evaluating them at r₀ is valid; dropping the 1/(1+2r) on the log term is a further upper bound. ✓

**Numbers.**
- RO0001 (λ = 13.308, α₀ = 0.9927): b₁ = 3.494 and b₂ = 2.580, against Bellotti's 0.711 / 2.113. With Z = 5.558691 this gives b₁+b₂Z = 17.84, against 12.46 for her λ = 1 box (×1.43).

**Why the gain is real.** b₂Z dominates b₁ (δL ≥ 1/Z ≈ 0.18, so the "+2 zeros" constant costs 2Z ≈ 11), and it hardly depends on λ. Meanwhile the off-diagonal harmonic sum, which dominates Hn for λ = 1, shrinks like (2/λ)log(1/(λν)). My own code, at RO0001's parameters with L = 29 (decoupled b's):

| λ | Hn | b₁+b₂Z | Hn·(b₁+b₂Z) | C |
|---|----|--------|--------------|---|
| 1 | 11.952 | 12.170 | 145.5 | 38605 |
| 4 | 3.558 | 13.228 | 47.1 | 12490 |
| 8 | 2.033 | 15.065 | 30.6 | 8128 |
| 13.308 | 1.541 | 17.836 | 27.5 | 7293 |
| 20 | 1.323 | 21.890 | 29.0 | 7684 |
| 30 | 1.190 | 29.232 | 34.8 | 9229 |

So the optimum λ ≈ 13 and the ×0.19 gain are reproduced with ñ correctly scaled.

**Structural sanity check.** As λ → ∞, Hn → K (the diagonal plus one neighbour), while ñ ∝ λ. This is the usual large-values trade-off: well-spaced representatives make the Halász sum diagonal-dominated, and boxes of height O(1/log T) keep O(1) zeros each.

### 3.3 Is ñ = b₁δ log T + b₂ "still valid"?
Yes, with b₁, b₂ as functions of λ as above. A λ-independent ñ would be invalid, but the code does not do that.

### 3.4 The cosmetic gap (not addressed in REPORT.md)
TZ Prop 2.11 is stated for disc centres with 3·10¹² ≤ |t| ≤ T, and the code uses log T.
- A box of height λδ ≈ 0.07–0.26 can have its centre up to λδ/2 above T (top box) or below 3·10¹² (bottom box).
- Bellotti has the same issue at scale δ; her code uses log(T₀ + r).
- **Fix (no numerical change).** Only zeros with 3·10¹² < γ ≤ T are counted. Replace each box by its sub-box [max(t₀, 3·10¹²), min(t₀+λδ, T)]. This sub-box is no taller, its centre lies in [3·10¹², T], and it fits in the disc of radius ρδ about its own centre.
- This should be one sentence in the write-up.

## 4. Other fixes, spot-checked

- **(a) |G(½+it)|.**
  - The paper (after (4.14)) claims |G(½+it)| ≤ (W²)^{1/2}|G(1)|. This is invalid: G(1) = Σθ_jθ_k/[j,k] is a signed sum of size about 1/log W, whereas the absolute sum is not. The paper's step bounds the absolute sum by G(1).
  - My derivation: write [j,k]^{−1/2} = (jk)^{−1/2}Σ_{e|(j,k)} h(e) with h = μ∗(·)^{1/2} ≥ 0 (h(p) = √p−1) and |θ_j| ≤ log(W/j)/log W. Use Σ_{m≤Y} log(Y/m)m^{−1/2} ≤ ∫₀^Y = 4√Y, since the integrand is decreasing. Then |G(½+it)| ≤ (16W/log²W)·Σ_{e sqfree} h(e)/e² = 16·P_h·W/log²W. This is exactly Phase 0's bound.
  - P_h: my Arb product over p ≤ 2·10⁵ with tail e^{2/√P} gives P_h ≤ 1.478591; Phase 0 has ≤ 1.48111. ✓
- **(b) d₃.**
  - The paper's (3.6) with Lemma 3.2 gives d₃ = 4·1.0061(uL+1.333+…+1)/((v−u)²L).
  - Her code's `Psisquare` = 4(1+1.0061(uL+…))/((v−u)²L³). It is too small by L². ✓ (Moot: OPT_CORR/IMPR use d₄ = 'rza'.)
- **(c) Lemma 3.2 and RZA.**
  - Of the four terms of log²(V/U)Ψ², the (Λ₂,Λ₂) term needs Lemma 3.1 with z₁ = z₂ = V. That requires V² < N and gives log V, whereas the paper uses UV < N and log U. ✓ (The cross terms are fine in absolute value, because Graham's main term is a non-negative Selberg form.)
  - **RZA Cor 1.2 (arXiv v1).** Σ_{n≤X}Ψ²(n)/n ≤ 3.09·log X/log(z₂/z₁)·(1.084(τ+1)+1.301(1+τ²)−0.116)/(τ−1) for X ≥ z₁ ≥ 100, z₂ = z₁^τ. The RZA weights coincide with ψ_d for (z₁, z₂) = (U, V).
  - The constants are consistent with RZA's own proof: e^{1+γ/log 100} = 3.0813 ≤ 3.09, the B(1+τ²) − C/e step gives C/e = 0.11699 ≥ 0.116, and there is a single factor (τ−1) since log²(z₂/z₁) = (τ−1)log z₁·log(z₂/z₁).
  - **Partial summation.** A(y) = 1 for y < U (Ψ(n) = 0 for 2 ≤ n ≤ U), and A(y) ≤ K log y for y ≥ U with K = F(τ)/((v−u)L). Then Σ Ψ²(n)/n·e^{−n/X} ≤ (U−1)/X + K(log X − γ_E + 1/X) ≤ T^{u−x} + F(τ)x/(v−u). ✓
  - UNSURE: the published version of RZA was not seen.
- **(d) (3.10).** |M(1)| ≤ Σ_{n≤VW} d²(n)/n ≤ d₂ log⁴(VW) = d₂(v+w)⁴L⁴, whereas the paper and code have (u+w)⁴. ✓ The corrected code uses the Σ_{n≤VW}d²/n bound directly.
- **(e) Lemma 2.7.**
  - d₁(x) = D₁ + D₂/log x + … is decreasing, so ∫₁^X d₁(u)log³u/u du ≠ d₁(X)·∫…. ✓
  - Her `fracd2` calls `contrd2(u,v,w,x)` with argument order (u,x,v,w), so it evaluates at T^{w+x}. ✓
  - The replacement `_D2fixed` is a correct partial summation of CHT19 Thm 2. I re-derived the 0.5, 153.588 and 1.0324 terms independently.
- **(f) K.** Re-derived in §2. Phase 0 uses the lower end of κ (which gives the largest K). ✓

Other small points I checked: the (3.20) replacement tail (|ΨΘ| ≤ d(n)² ≤ 4n gives 4∫_{U−1}^∞ye^{−cy}dy), the c₅ J-integral bounds J₁…J₄ (re-derived), and the contour shifts (the pole of Γ at s = 0 contributes 0 because X⁰ − Y⁰ = 0, or because ζ(ρ) = 0 in Lemma 3.4).

**Patel–Yang.** 66.7·t^{27/164} holds for t ≥ 3 (arXiv:2302.13444 abstract; JNT 262 (2024)), so its use at all heights in c₁ and c₅ is legitimate. ✓

## 5. Independent numerical check (item 5)

**Code.** `indep_C.py` is my own python-flint implementation, written from §2–3. It imports nothing from Phase 0.
- 1-d integrals are upper Riemann sums of monotone integrands with explicit tails (not `acb.integral`).
- |Γ| integrals use plain Arb box enclosures.
- The row supremum is taken over L-balls of width 0.02 (at most 400 pieces).
- **Joint mode** (my default): sup over δ ∈ [ν, 1−α₀] of A·ñ(δ)/(δL), with decreasing terms evaluated at the left end and increasing terms at the right end of 64 δ-cells. This is tighter than Phase 0's decoupled b₁ + b₂Z.
- **Decoupled mode**: reproduces Phase 0's b₁ + b₂Z, used to check that the code is faithful.

**Spot rows** (refereed unless noted; B = 2x on every row; c₁ > 0 and c₁²−c₅ > 0 on every piece; U ≥ 100; r₀ < ½; d* ≤ ½):

| id | log T | α₀ | λ | C_csv | C_ref joint | ratio | C_ref decoupled | ratio |
|----|-------|----|---|-------|-------------|-------|-----------------|-------|
| RO0001 | 28.73–29 | 0.9927 | 13.308 | 7460.59 | 7187.29 | 0.9634 | 7437.44 | 0.9969 |
| RO0005 | 28.73–29 | 0.9927 | 13.371 | 4586.17 | 4412.03 | 0.9620 | 4570.44 | 0.9966 |
| RO0019 (BTY 4.896) | 28.73–29 | 0.9927 | 12.847 | 4191.60 | 4140.85 | 0.9879 | 4176.71 | 0.9964 |
| RO0635 | 49–50 | 0.9899 | 12.730 | 4856.90 | 4011.82 | 0.8260 | 4846.77 | 0.9979 |
| RO0665 | 50–51 | 0.9892 | 12.336 | 5132.76 | 4156.48 | 0.8098 | 5104.71 | 0.9945 |
| RO1383 | 79–80 | 0.9860 | 11.159 | 5911.84 | 4377.61 | 0.7405 | 5876.71 | 0.9941 |
| RO1392 | 79–80 | 0.98 | 9.728 | 7173.07 | 4811.03 | 0.6707 | 7163.47 | 0.9987 |
| RO1396 | 80–82 | 0.9850 | 10.944 | 6111.09 | 4449.61 | 0.7281 | 6101.75 | 0.9985 |
| RO1468 | 98–100 | 0.9850 | 10.932 | 6193.08 | 4463.86 | 0.7208 | 6163.10 | 0.9952 |
| RO1476 | 100–102 | 0.9850 | 11.107 | 6201.02 | 4445.39 | 0.7169 | 6171.45 | 0.9952 |

**Point comparison** (`cmp_point.py`, RO0001 at L = 28.9). d₄, d₅ and b₁+b₂Z agree with belarb to all digits. Hn is 0.7% lower in mine, only because my J₁ is ⌊·⌋+1 rather than ⌊·⌋+2. c₁ agrees to 4·10⁻⁵ and c₅ to 0.4% (my c₅ is the smaller); the remaining differences come from different but valid integral bounds (`cmp_point_RO0001.txt`).

**Full files** (`batch_check.py`, final run with tightened Γ constants):

| file | mode | rows | C_ref/C_csv min / median / max | rows with any failure |
|------|------|------|-------------------------------|------------------------|
| rows_reopt.csv | joint | 1596 | 0.658 / 0.739 / **0.98858** | **0** |
| rows_reopt.csv | decoupled | 1596 | 0.985 / 0.9985 / 1.0079 | 39, all with ratio > 1 (see below) |
| rows_reopt_lam1.csv | joint | 266 | 0.927 / 0.951 / 0.9978 | **0** |
| rows_reopt_lam1.csv | decoupled | 264 | 0.9996 / 0.9998 / 1.00002 | 1 (RL0025, see below) |

The joint-mode run is the referee's rigorous bound.
- **Every row of rows_reopt.csv and rows_reopt_lam1.csv** has C_csv ≥ C_ref, B = 2x, c₁ > 0 and c₁²−c₅ > 0 on every L-piece, U ≥ 100, x > u, r₀ < ½ and a correct status label.
- On λ=1 rows C_ref/C_csv is close to 1 (median 0.951) because ñ hardly depends on δ when r₀ is small. On λ≈10–13 rows it is lower (median 0.739), from the joint δ-sup.

The decoupled mode is a fidelity check only.
- **The 39 + 1 excesses are Arb dependency on my coarse L-balls.** 19 of the 39 are the wide rows from e^170.2 up, where pieces are up to 0.25 wide because of the 400-piece cap; their max ratio is 1.0079. The other 20 are rows with α₀ ∈ {0.98 (16), 0.985 (3), 0.986 (1)}, with excesses ≤ 3.7·10⁻⁴.
- **Re-runs with fine pieces fall below C_csv:**
  - RO1589 [300, 400]: 0.99952
  - RO1581 [200, 250]: 0.99962
  - RO0728: 0.99657
  - RO0667: 0.99636
  - RL0025: 0.99905, with pieces of 5·10⁻⁴
- I did not re-run all 40 with fine pieces; the joint mode already passes them.

Earlier run: with my first, looser Γ-box constants (box cells touching σ′ = −½ give wide Arb enclosures), joint mode still passed all 1596 rows (max ratio 0.9888). The decoupled excesses of up to 0.9% that appeared were entirely due to my c₅ being up to 3.6% larger (α₀ = 0.98); tightening the σ-grid removed them (`run1_loose/`).

## 6. Other observations (item 6)

1. **Conventions.** The proof handles N(σ,T) = #{β ≥ σ, 0 < γ ≤ T} with closed boxes; strictness is never used. Bellotti states σ < β < 1, 0 < γ < T; the closed version is stronger and is what the rows claim. ✓
2. **Low zeros.**
   - Zeros with γ ≤ 3·10¹² have β = ½ (Platt–Trudgian), so all counted zeros have γ > 3·10¹². This justifies `gmin = 3e12` in c₁, which is stronger than her γ > 0.447 log T. ✓
   - The rows with logT0 = 28.7296 < log 3·10¹² are computed from log 3·10¹²; below that N = 0. ✓
3. **Zero-free inputs.**
   - The rows use max(classical, Ford for L ≥ 33, Littlewood) at T, which needs each width valid and non-increasing on [3·10¹², T].
   - Phase 0 checks that Ford is decreasing, and uses classical as a fallback below 1.88·10¹⁴ (ν_cl(1.88·10¹⁴) ≈ 0.00547 ≥ ν_Ford(e³³) ≈ 0.00489; I recomputed both). ✓
   - UNSURE (inherited, not checked here): the exact statement and validity range of Ford/Yang (1.4), and Yang's 21.233 Littlewood region. Status labels (refereed / audited preprint for cl4.896) are consistent on every row.
4. **Looseness, not error.** The decoupled ñ/(δL) ≤ b₁(r₀) + b₂(r₀)Z takes the cubic term at δ_max and the 2/(δL) term at δ = ν simultaneously. My joint sup gives C up to 34% smaller (median 26% smaller) on rows_reopt. This is a free improvement if wanted, and would itself need a referee check.
5. **α₀ = 0.98 rows** (below Bellotti's 0.985). Every α₀-dependent constant is recomputed for the actual α₀, and no remaining step needs α₀ ≥ 0.985: g = 1 needs 2−2α₀ ≤ 1, and the Γ ranges σ′ ∈ [−½, 3/2−2α₀] avoid the pole at 0. ✓
6. **Code nits.**
   - `check_hypotheses` labels a check "r₀ ≤ 1/30 (b1 = rho/2 exact)" but does not test it. Harmless, because `b12` uses max(½, f(r₀)).
   - `counting_check.py` ignores far pairs; my `adversarial_Hn.py` includes them.
   - REPORT says J₁ = ⌈1/(λν)⌉, while the code uses ⌊·⌋+2, which is conservative.
   - Her 4.05206 is ∫_{−∞}^{3}|Γ| at σ′ = −0.47 (her (4.18)), not ∫_ℝ. This is irrelevant, since IMPR uses recomputed constants.
7. **Not checked by me** (UNSURE):
   - Rows above e^{3000} and the KV row.
   - rows_corrected_faithful.csv under its own option set (OPT_CORR). My code evaluates IMPR only. Since IMPR is a valid bound, C_corr ≥ my IMPR value only shows the CORR rows are true statements, not that the CORR computation is right.
   - The JNT published version of Bellotti, versus arXiv v2.

## 7. Deliverables and how to re-run
All files are in `work/review_phase0/`:
- `indep_C.py`: the independent evaluator. Run `python indep_C.py <csv> id1,id2,… [decoupled]`.
- `batch_check.py`: whole-file check. Run `python batch_check.py <csv> step offset joint|decoupled [piece_width]`; it takes a few minutes per shard of 400 rows.
- `cmp_point.py`: component-by-component comparison with belarb at one L. This is the only script that imports Phase 0 code.
- `adversarial_Hn.py`: float worst-configuration check of Hn; it takes about 13 minutes.
- Outputs:
  - `batch_*.txt` and `lam1_remaining.txt`: final run; the numbers in §5 come from these.
  - `adversarial_Hn.out`.
  - `out_joint.txt`, `out_decoupled.txt` and `run1_loose/`: early runs with looser Γ constants, kept for the record.
