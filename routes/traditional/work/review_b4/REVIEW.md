# Referee report: the repaired b₄ lemma ("Theorem R", `work/audit_rza/repair/`)

*Independent adversarial review, 2026-11-06. Folder `work/review_b4/`; nothing outside it was modified. The audit tree was copied to `rerun/` and re-run there. All my own scripts are new code and share nothing with `audit_rza/`.*

**Object under review.**
> **Theorem R.** S_ε(X) = Σ_{d,e≤X} μ(d)μ(e)/[d,e]^{1+ε} ≤ 0.5159 for all real X ≥ 3·10¹² and 0 < ε ≤ 0.0227.
> The "Helfgott-free" version gives 0.5161.

## 0. Bottom line

| # | Item | Verdict |
|---|---|---|
| 1 | Corrected identity (R.1), with X^{−ε} decay; comparison with RZA (6.6) | **CONFIRMED** (re-derived from scratch; checked numerically) |
| 2 | Every step of the proof, the X- and ε-ranges, external inputs | **CONFIRMED**. No error that affects the result. Minor issues are listed in §2.9 |
| 3 | Arb certification (re-run and code inspection) | **CONFIRMED**. `run_all.py --full` gives 0 FAIL in 26 min 47 s on 16 cores, with identical numbers. No float leak or wrong rounding direction in a claimed quantity |
| 4 | Independent numerics (X ≤ 10⁷) | **CONFIRMED** (sanity only). S_ε stays ≤ 0.4446 for N ≥ 1000. The decay per decade is X^{−ε}, not X^{−2ε}. The main term of the weighted bulk matches to 2·10⁻⁶ |
| 5 | Coverage of the Chourasiya–Simonič (CS) use | **CONFIRMED**, with a label correction: the lemma is **CS v2 Lemma 6** (`lem:fxone`), not Lemma 7. The quantity and normalisation are the same, and the hypotheses are covered (§5) |

**Most serious problem.** There is no mathematical error in Theorem R. The points that matter for using it are about tier and citation:
1. **The CS lemma number.** CS v2 `InghamPostArXiv.tex` l.644–669 is **Lemma 6** in both v1 and v2; the PDF text agrees. The repair REPORT, the audit REPORT, the brief and `phase1_cs/cs_bounds.py` all call it "Lemma 7" (Lemma 7 is `lem:3/2`).
2. **"Helfgott-free" is not literally free.** Zuniga-Alterman 2022's E₁⁽²⁾ = 0.232 still carries one term that derives from Helfgott's book. In ZA's Sage source (`audit_rza/deps_lit/dl/za22/x/…v3.sagetex.sage`, l.566):
   CONSTANT2 = (1−1/√2)·max(4·C_sum2_22/π², 3·9/70, 0.40672).
   - The book-derived term is 3·9/70 = 0.386. It does **not** bind: the maximum is 4·C_sum2_22/π² = 0.7896.
   - So the book is needed only in the much weaker form "its constant is ≤ 0.263". *We infer this from the Sage code; UNSURE until ZA's proof text is read.*
   - The repair REPORT §5 flags the dependence but treats it as full ("∂b₄/∂E₁⁽²⁾ = 0.063").
3. **Where the result is load-bearing.** The supremum sits at ε → 0⁺ and equals Tail₀ + Bulk₀ (the corrected RZA Theorem 1.1 at X₀ = 3·10¹²). At the other end, ε = ε₀, the margin is only 0.090, and this is about the size of the cross-term bound T₄(ε₀) = 0.088.
   - If T₄ were under-estimated by a factor ≥ 2.03, the supremum would move to ε₀ and exceed 0.5159.
   - I re-derived T₄ and found it correct (§2.4). It is the one O(ε) term whose correctness matters.

**Can it be used?** Yes.
- **b₄ = 0.5161** (Helfgott-free) at tier **"refereed + audited preprints (RZA §4–5 lemmas, re-derived by the audit) + own new lemma (Theorem R, now reviewed)"**. The caveat is the non-binding ZA/book term of point 2.
- b₄ = 0.5159 additionally uses Helfgott's unrefereed book directly, through RZA Lemma 2.5 (its inputs are RZA Lemmas 2.2–2.3).
- Neither value is "refereed only". CS itself is a preprint anyway.

## 摘要（中文）

- **结论：Theorem R 成立，可以使用。** 我没有发现影响结果的错误。
  - 恒等式 (R.1) 由我从头推导，结果一致；衰减是 X^{−ε}。RZA (6.6) 把 (X/ℓ)^{−2ε} 写成了 X^{−2ε}，因此是错的。
  - 证明各步逐一复核；数值上逐项检查了 98 个不等式，0 个失败。
  - `--full` 重跑结果为 0 FAIL，耗时 26 分 47 秒，数值完全一致。
- **独立数值检验**（X ≤ 10⁷，只能检验趋势）：
  - S_ε 随 ε 递减，衰减速度约为 X^{−ε}；
  - 主项常数独立复算（W、W^h、S₁₁、S₁₂ 用子集穷举）后完全吻合。
- **CS 的用法已覆盖。** 但用到 b₄ 的是 **CS v2 的 Lemma 6**（`lem:fxone`），不是 Lemma 7，引用需要更正。
- **层级。**
  - b₄ = 0.5161 属于“refereed + 已审 preprint（RZA §4–5）+ 本项目已审引理”这一层。
  - “Helfgott-free”并不完全：ZA 2022 的 E₁⁽²⁾ 里仍有一项来自 Helfgott 书稿。按 Sage 源码，这一项 3·9/70 不是 max 的取值项，所以只需要一个弱得多的形式（我们推断，UNSURE）。
- **可以删掉的输入：** A10（9.1）和 Ramaré 2015 Cor 1.10（F₁ ≥ 0 只需 x ≤ 47，已有 Arb 证明）。
- **关键承重项是 T₄：** 若 T₄ 被低估 2 倍以上，ε₀ 处的界就会超过 0.5159。我已复核 T₄ 无误。

## 1. The identity (item 1): CONFIRMED

**Derivation (mine).** Let s = 1+ε and ℓ squarefree.
1. Since 1/[d,e]^s = (d,e)^s/(de)^s and (d,e)^s = Σ_{ℓ|(d,e)} φ_s(ℓ), with φ_s(ℓ) = ∏_{p|ℓ}(p^s − 1), we get
   S_ε(X) = Σ_{ℓ≤X} a_ℓ m_ℓ(X/ℓ; s)², where a_ℓ = μ²(ℓ)φ_s(ℓ)ℓ^{−2s}.
2. Σ_{(n,ℓ)=1} μ(n)n^{−s} = P_ℓ/ζ(s), with P_ℓ = ∏_{p|ℓ}(1−p^{−s})^{−1}. Write m_ℓ(Y;s) = n_ℓ(Y) + P_ℓ/ζ. Then a_ℓP_ℓ = μ²ℓ^{−s} and a_ℓP_ℓ² = μ²/φ_s(ℓ).
3. Σ_{ℓ≤X} μ²(ℓ)ℓ^{−s} m_ℓ(X/ℓ;s) = Σ_{N≤X} N^{−s} Σ_{ℓn=N, (ℓ,n)=1} μ²(ℓ)μ(n) = 1. Hence
   S_ε = Σ a_ℓ n_ℓ² + 2/ζ − G(X)/ζ², with G(X) = Σ_{ℓ≤X} μ²/φ_s(ℓ).
4. By the definition of Δ in RZA Lemma 3.1 (valid for Y ≥ 1, i.e. ℓ ≤ X), n_ℓ(Y) = Y^{−ε}(m_ℓ(Y) + εΔ_ℓ(Y,ε)). Moreover a_ℓ(X/ℓ)^{−2ε} = μ²φ_s(ℓ)X^{−2ε}ℓ^{−2}. Therefore

  **(R.1)** S_ε(X) = Σ_{ℓ≤X} μ²(ℓ)φ_{1+ε}(ℓ)X^{−2ε}ℓ^{−2}(m_ℓ + εΔ_ℓ)² + 2/ζ(1+ε) − G(X;1+ε)/ζ(1+ε)².

   Using φ_{1+ε}(ℓ) = φ(ℓ)ℓ^ε c_ε(ℓ), with c_ε(ℓ) = ∏_{p|ℓ}(1 + (1−p^{−ε})/(p−1)), the weight is X^{−ε}b_ℓ c_ε(ℓ)(ℓ/X)^ε.

**Comparison.**
- This is exactly the repair's (R.1) and the audit's §3 formula.
- RZA v3 (`OnADoubleMobiusSum-20.tex` l.1466–1489) first uses φ_{1+ε}/ℓ^{2+2ε} ≤ φ/ℓ² correctly. It then writes n_ℓ(X/ℓ)² = **X**^{−2ε}(m+εΔ)², whereas the correct factor is (X/ℓ)^{−2ε}. This drops the factor ℓ^{2ε} ≥ 1, so (6.6) is false.

**Numerical confirmation (`pieces_check.py`, float).**
- (R.1) reproduces S_ε(X) to ≤ 10⁻¹⁰ at X = 2·10⁴, 10⁶ and 3·10⁶ (real X = N + ½), for ε ∈ {10⁻⁴, 10⁻³, 10⁻², 0.0227}.
- The right side of RZA (6.6) is smaller than S_ε(X) in every case; for example 0.2508 vs 0.3354 at X = 3·10⁶, ε = 0.0227.
- `sanity_Seps.py`: the decade maxima of S_ε decay by a factor of about 10^{−ε}, not 10^{−2ε}:
  - ε = 0.01: 0.40216 → 0.39322, ratio 0.9778, against 10^{−0.01} = 0.9772;
  - ε = 0.0227: ratio 0.952, against 10^{−0.0227} = 0.949;
  - X^{−2ε} would give 0.955 and 0.901 respectively.

## 2. The proof, step by step (item 2): CONFIRMED

Each step below was re-derived by hand, and each inequality was also checked numerically at X = 10⁶ and 3·10⁶ (`pieces_check.py`; 98 checks, 0 FAIL).

### 2.1 Lemma R1 (weights)
- (a) w_ℓ ≤ b_ℓ(ℓ/X)^{2ε} ⟺ (p^{1+ε}−1)/(p−1) ≤ p^{2ε} ⟺ 1 ≤ p^ε(p−1). True.
- (b) w_ℓ ≤ X^{−ε}b_ℓ h(ℓ)^ε(ℓ/X)^ε, because c_ε(p) = 1 + (1−p^{−ε})/(p−1) ≤ 1 + ε log p/(p−1) ≤ p^{ε/(p−1)}. True.

Both hold termwise in the numerics.

### 2.2 Step 3 (ℓ > X/10.9, i.e. Y < 10.9)
Inputs:
- Δ ≤ 0: sign table 4a, Arb-certified for ε ≤ 4/25 and re-run.
- εΔY^{−ε} ≥ −P/ζ, which is equivalent to m_ℓ(Y;1+ε) ≥ Y^{−ε}m_ℓ(Y). This reduces to F₁ ≥ 0 on [1, Y].

**Simplification.** F₁ ≥ 0 is needed only for Y < 10.9, and it is **Arb-certified for x ≤ 47 and all q** in `audit_rza/lemma31/check_m_values.py` (5). So Ramaré, Math. Comp. 84 (2015), Cor 1.10 is not needed. The repair REPORT's A2 lists it as needed.

The square terms then cancel against G exactly: the bound is (G(X) − G(X/10.9))/ζ². Cross terms:
- they are ≤ 0 when m ≥ 0 (which holds for Y < 5);
- otherwise m ≥ −1/30, and 1/ζ < ε gives (2ε/30)X^{−ε}μ²(ℓ)/ℓ;
- summing with Ramaré 2016 Lemma 3.4 (needs X/10.9 ≥ 10³) gives ax₁ = 0.0160591.

All correct.

### 2.3 Step 4 (cross terms, ℓ ≤ X/10.9): T₄ + T₅
**The bound m_ℓΔ_ℓ ≤ (19/210)|Δ_ℓ| on 10.9 ≤ Y < 47.**
- Class 1 means (ℓ, ∏_{p≤43}p) = 1. Then m_ℓ(t) = m(t) for t < 47, and |m(t)| ≤ 19/210 there.
- All other classes have Δ ≤ 0 (4b and 4d) and m ≥ −2323/30030.
- This was checked exactly by the audit, and holds for every ℓ in my numerics.

**For Y ≥ 47**, mΔ ≤ |Δ| because |m_q| ≤ 1 (Granville–Ramaré 1996).

**The √-part of A1** gives
- Σ_{ℓ≤X/Z} b_ℓ(√ℓ/φ_{½}(ℓ))/√(X/ℓ) = Ξ₁(X/Z)/√X (no g₀), and
- the same sum with g₀ is Ξ₂(X/Z)/√X (RZA Lemma 4.10 definitions, l.1017–1028).

So T₄ is right: a_ε goes with THxxx = 2.5878 (Ξ₁) and 4.1g₀ goes with THx = 1.8222 (Ξ₂). My sieve to 10⁷ gives sup Ξ₁/√X = 2.25342 and sup Ξ₂/√X = 1.58799. The split "1 = ax₂ + (1−ax₂)" is right.

**Log part, Lemma R3.**
- I redid the partial summation. It uses that φ_ε(t) = (X/t)^{−2ε}/log(X/t) is increasing, that mx − mm ≥ 0 and mm > 0 (asserted in the code), and that ∫ φ_ε dt/t ≤ E₁(2εL₀).
- Correct. The lower bound K₁(t) ≥ c₁ log t + mm is needed for all real t ≥ 1; mm is taken as inf_N(K₁(N) − c₁ log(N+1)), which covers this.

### 2.4 Step 5 (square terms): T₆
- Bohr's inequality applies, and the expansion (4.1g₀ + a)² = 16.81g₀² + 8.2ag₀ + a² pairs with Σ₁/TH1, σ₂/THx2 and σ₁/THx1 (RZA Lemma 4.5 definitions, l.950–963). Correct.
- The log part uses LL₂ = c₂/L₀ + (log2mx − min(log2mm, 0))/L₀². I re-derived this. It is correct, including the sign fix of the audit's I4.

### 2.5 Step 6: T₇
- The bound is correct.
- **Simplification.** Input A10 (G(10⁸; 1.1) ≥ 9.1) is **not needed**. Replacing T₇ by 2ε (using only G ≥ 0) leaves the supremum unchanged at 0.5158745 (rza) and 0.5160912 (hf) (`F_grid.py`), because 9.1ε² matters only at large ε, where F is far below its supremum.

### 2.6 Step 7 (main term)
**Tail.** w ≤ b(J+0.9999)^{−2ε} for Y ≥ J+0.9999. RZA Lemma 5.1 (valid for X ≥ D > 0) gives Tail₀ = 2TH1/Z + 2√2H₁L₁/√Z + H₁²L₂. I re-derived it, including L₁ = 2TH2/log N and L₂ = TH3/log N.
- At X = 3·10⁶ the true S₀** is 0.0013, far below 0.0619. The bound is very conservative.
- TH1 = 2.1205 is the Theorem 4.1 analytic value at X = 4·10⁹. The scan maximum is only 2.0680, at X = 42 (my sieve to 10⁷ agrees: 2.06804 at 42, and 2.00001 at 10⁷).

**Bulk.** R1(b), then Hölder with t = ε/ε₀ ∈ (0,1]. This is valid, since h^ε = (h^{ε₀})^t and A^{1−t}B^t is increasing in A and B.

**Lemma R5 (weighted bulk).** The decomposition is RZA (5.3) with b_ℓ c(ℓ), c multiplicative and ℓ = nℓ′, (ℓ′, Π(j)) = 1. Then:
1. Apply ZA 2022 Thm 4.6 = RZA Thm 4.2[A] with α = 1 and f(p) = (p−1)c(p)/p². This f satisfies f(p) = 1/p + O(log p/p²), so β − α > ½. The theorem is stated for X > 0.
2. The main term is H_f^q(0)φ(q)/q = W^c r^c_q. The error constant is t_q w^q P.
3. The j = J block is only partially in range; extending it to the full range is an over-count of non-negative terms. So is including all n | Π(j) (main and error parts are both ≥ 0).
4. Small Y need no special care: when X/(nj) < 1 the true block is 0.

Everything is correct.

**Independent recomputation of the constants (`consts_check.py`).** Float, over primes ≤ 10⁸. S₁₁, S₁₂ are computed by brute force over all subsets n | Π(j); the audit uses a pair-sum identity instead.

| constant | mine | repair |
|---|---|---|
| W | 0.428249506119 | 0.4282495061 |
| W^h | 0.432358091513 | 0.4323580916 |
| G₁, G₂ (p ≤ 10⁸, no tail) | 2.968189, 1.147887 | 2.9682236, 1.1478998 (with tail) |
| G₁^h, G₂^h | 2.863613, 1.101533 | 2.8636589, 1.1015508 |
| S₁₁(68), S₁₂(68) | 0.332879289369, 21924.043941 | identical |
| S₁₁^h(68), S₁₂^h(68) | 0.335794912816, 23491.956864 | identical |
| J = 69 values (hf variant) | 0.332946088592, 23212.2475; 0.335862880457, 24874.1009 | identical |

**Numerical bulk check.** The main term W^c(log 2 + S₁₁^c(68)) is matched by the true sum Σ_{ℓ>D} b_ℓc(ℓ)m_ℓ(X/ℓ)²:

| X | c = 1 | c = h^{ε₀} |
|---|---|---|
| 10⁶ | 0.439404 (main term 0.439396) | 0.444880 (main term 0.444871) |
| 3·10⁶ | 0.439394 | 0.444870 |

### 2.7 The ranges of X and ε
- **X.** Every X-dependent factor (X^{−ε}, X^{−½}, 1/log X) is decreasing, so X = X₀ is the worst case. The constraints X/10.9 ≥ 10³ (Lemma 4.3) and X/10.9 ≥ 10⁸ (A10, now unnecessary) hold. Real X is allowed: every lemma used is stated for real X, and S_ε is a step function.
- **ε.** Lemma 3.1 is used with ε ≤ 1, and sign table 4a needs ε ≤ 4/25; both hold. Hölder needs t ≤ 1. On the ε → 0 side, the first cell [0, 10⁻⁹] uses uE₁(u) < u log(1+1/u) (Abramowitz–Stegun 5.1.20) together with the monotonicity of u log(1+1/u). This is valid.
- **Sign of the slope.** F decreases from F(0⁺) = Tail₀ + Bulk₀, with slope ≈ −6.5 near 0. The term εlog(1/ε) from T₅ would dominate only for ε < e^{−150}, and the first cell bounds it directly.

### 2.8 External inputs and their status
"Book" means Helfgott, *The ternary Goldbach problem*, book manuscript, 2019, unrefereed.

| input | used for | status | notes |
|---|---|---|---|
| RZA Lemma 3.1 \|Δ\| bound (0.03, 4.1, (5+ε2^ε)/2) | T₄, T₅, T₆ | IF Thm 1.4/1.7 (Ramaré–Zuniga Alterman, Math. Comp. 2026, refereed) + RZA Lemma 2.5 | rza variant: the book enters through Lemma 2.5. hf variant: IF's proof inequality + own R2′ |
| sign table 4a/4b/4d, m-patterns | Steps 3, 4 | own Arb / exact | re-run, 0 FAIL |
| F₁ ≥ 0 | Step 3 | own Arb for x ≤ 47 (sufficient) | Ramaré 2015 Cor 1.10 **not needed** |
| \|m_q\| ≤ 1 | Step 4 | Granville–Ramaré, Mathematika 1996 | refereed |
| Ramaré 2016 Lemma 3.4 (1.040, 1.048) | ax₁ | refereed | |
| 1/ε < ζ(1+ε) ≤ e^{γε}/ε | Steps 3, 6; also CS | refereed | |
| RZA Lemmas 4.5, 4.6, 4.8, 4.10, 4.11, 4.13, Cors 4.7, 4.9, 4.14, Lemma 5.1, Lemma 5.2 | Tail₀, Bulk₀, T₄–T₆ | preprint, re-derived and recomputed by the audit (corrected W, c₁, log2mx/mm) | spot-checked here (W, G, S₁₁, S₁₂, σ/Σ/Ξ scans to 10⁷) |
| ZA 2022 Thms 3.3/4.6 (E₁⁽¹⁾ = 1.044, E₁⁽²⁾ = 0.232) | Lemmas 4.5–4.13, 5.2, R5 | refereed (Colloq. Math. 168) | E₁⁽²⁾: book term non-binding (point 2 of §0); D₁ = 0.43 (Ramaré 2019) also non-binding |
| Dusart 2018 | Euler tails | refereed | |
| \|m\| ≤ 0.0144/log x, x ≥ 96955 | hf variant | Ramaré, Math. Comp. 84 (2015), Thm 1.2, refereed | statement seen only through secondary citation (Helfgott book, DEPS.md l.97) |
| \|m\| ≤ √(2/t), \|m₂\| ≤ √(3/t), t ≤ 10¹⁰ | hf variant | own float certificate with a-priori error bound | re-run, OK |
| \|m\| ≤ √(2/t) to 10¹², \|m₂\| ≤ √(3/t), 0.0296; FA-II's 0.010032 | rza variant only | **book** (FA-II itself is refereed, but uses book Lem 5.10) | |

**How the Helfgott-free version avoids the book.** It replaces Lemma 2.5 by R2′, with threshold N = 10¹⁰ and the following inputs:
- the own √-certificate;
- Ramaré 2015 (H′ = 0.0144);
- H₂′ = 0.029762, derived from m₂(t) = Σ_k 2^{−k}m(t/2^k). My float check gives 0.02976036 at t = N, decreasing in t.

It also replaces the 0.03 of Lemma 3.1 by C_log = 2^{ε₀}T_N H′/log 2. Here T_N = 1.0346 (my mpmath value: 1.034537 at y ≈ 1.02·10¹³). The repair's analytic tail bound for u ≥ 3 log N is correct; I re-derived it by repeated integration by parts.

Everything that depends on N was then recomputed (Euler products, scans B, C, E, F). The cost is +2.2·10⁻⁴ on b₄.

### 2.9 Minor issues (none affects the result)
1. **REPORT §3 Step 9** says "every factor of F is monotone in ε". This is false for uE₁(u), which increases only up to u ≈ 0.435, while u = 2εL₀ reaches 1.25. The code uses the valid cell bound u_hi·E₁(u_lo), so the certificate stands.
2. **Unnecessary inputs** A10 (9.1) and Ramaré 2015 Cor 1.10 (F₁ ≥ 0) can be dropped; see §2.2 and §2.5.
3. **The CS label "Lemma 7"** should read Lemma 6 everywhere: the repair REPORT, `audit_rza/REPORT.md` §8, the `phase1_cs` docstrings and the brief.
4. **"Helfgott-free" wording**: see point 2 of §0. It is better phrased as "no direct use; one non-binding term inside ZA 2022".
5. **Robustness.** The result survives T₄ ×2, T₅ ×10, T₆ ×10, Hölder λ ×3, and dropping the G-term, but **not** T₄ ×3 (which gives 0.601). T₄ is the load-bearing O(ε) bound (§0, point 3).

## 3. Arb certification (item 3): CONFIRMED

**Re-run.** `python -I run_all.py --full` was run in `rerun/audit_rza/repair/` (a copy of the audit tree):
- 0 FAIL, **26 min 47 s** wall time on 16 cores;
- mcert to 10¹⁰: 539 s;
- sign table 4b: 480 s;
- hf scans E, F: 315 s;
- output `rerun/run_all_full_output.txt`;
- b₄ = 0.5159 / 0.5247 / 0.5161 / 0.5249, identical to the original.

The parent audit (`run_all.py --full`, which regenerates the rza-variant Euler products, the 4·10⁹ σ-scan and the S₁₁/S₁₂ sums) was also re-run, followed by `repair_bound.py`: 0 FAIL, byte-identical outputs and the same b₄ (§7).

**Code inspection.**
- `repair_bound.py`
  - All of it is Arb.
  - Each factor is evaluated at the correct cell end: decreasing factors at lo; increasing ones (ε, 2^ε, a_ε, ratio^{ε/ε₀}) at hi.
  - T₇ is increasing (its derivative 2 − 18.2ε(…) > 0), so it is evaluated at hi.
  - The cells cover (0, ε₀] contiguously: geometric cells 10⁻⁹·2^k up to 4.1·10⁻⁶, then uniform from 5.675·10⁻⁶.
  - Z = J+0.9999 is a tight ball; every value in it satisfies J < Z ≤ J+1.
  - The Bohr parameter c is free.
  - Assertions are present for mm > 0, Bulk₁ ≥ Bulk₀ and H₂′ ≤ the value used.
- `repair_hweights.py`
  - Arb throughout. W^h and P^h tails: c−1 ≤ 1.000001·ε₀ log p/(p−1) for p > 10⁸ (x ≤ 4.2·10⁻⁹).
  - The factor (1+f)(1−1/p) − 1 ≤ (c−1)/p ≤ 1.000001ε₀ log p/p², with the negative part dropped.
  - |pf−1| ≤ (1+1.000001ε₀ log p)/p, which I checked.
  - The upper bounds are taken correctly.
- `repair_mcert.py`
  - The float sieve has a sound a-priori bound. np.cumsum is sequential, so Higham's recursive-summation bound applies, and the code allows (L+2)u·Σ|x|·1.01.
  - The offset is propagated with fsum, and the endpoint condition |m(n)| ≤ √(2/(n+1)) is correct.
  - The Möbius sieve is correct: it uses all primes ≤ √N, and a cofactor > 1.5 means one large prime.
- `repair_hf_inputs.py`
  - Arb. The T_N cell bound uses u e^{−u} at the left end of each cell and li at the right end; this is valid.
  - The tail is checked (§2.8). The H₂′ sum over-counts both regimes, which is conservative.
- **Residual float content** (not mine to re-audit in full): the audit's σ/K-scans (`rza_scans.py`) use float with an a-priori error bound plus Arb at the extremal points.
  - Their outputs are dominated by analytic values (TH1, THx1, THx2, THxxx, THx), except mx, mm.
  - mx and mm enter only T₅ (≤ 4·10⁻⁶ at the worst cell).
  - My sieve to 10⁷ agrees with scan A where they overlap.

## 4. Independent numerics (item 4): CONFIRMED (sanity only)

**These checks do not prove anything at X ≥ 3·10¹².** The bound is claimed only for X ≥ 3·10¹²; at X ≤ 10⁷ it is far from tight, and these runs check only the trend and the internal consistency.

`sanity_Seps.py 1e7 0,1e-4,1e-3,5e-3,0.01,0.0227` computes S_ε(N) for every integer N ≤ 10⁷ in float64, in 5 min 15 s.
- It uses the increment formula from (d,e)^s = Σ φ_s.
- It is cross-checked against exact Fractions (ε = 0, N ≤ 300) and an Arb double sum (ε > 0, N ≤ 200). It agrees with `pieces_check.py` (the classic formula) at 10⁶ and 3·10⁶.

Maximum of S_ε(N) over each range of N:

| ε | [10³,10⁴) | [10⁴,10⁵) | [10⁵,10⁶) | [10⁶,10⁷) | S_ε(10⁷) |
|---|---|---|---|---|---|
| 0 | 0.444557 (N = 1321) | 0.441338 | 0.440860 | 0.440751 | 0.440732 |
| 10⁻⁴ | 0.444330 | 0.441008 | 0.440438 | 0.440236 | 0.440115 |
| 10⁻³ | 0.442300 | 0.438114 | 0.436669 | 0.435634 | 0.434619 |
| 0.005 | 0.433495 | 0.425999 | 0.420767 | 0.415996 | 0.411282 |
| 0.01 | 0.422977 | 0.411655 | 0.402158 | 0.393220 | 0.384487 |
| 0.0227 | 0.399051 | 0.378956 | 0.360571 | 0.343345 | 0.326995 |

What this shows:
- Small N can exceed 0.5159: S = 1 at N = 1, and S₀(13) = 0.5276. This is irrelevant, because Theorem R needs X ≥ 3·10¹². For N ≥ 100 the maximum is 0.4666 (at N = 101), and for N ≥ 1000 it is 0.4446 (at N = 1321, as RZA states).
- It decreases in ε at fixed X and decays like X^{−ε}, as the repair predicts.
- S₀ → 0.4407, matching Helfgott's limit.
- The repair's bound (0.5159) exceeds sup S₀ by about 0.075. This slack is mainly the crude Tail₀ (0.0619, against a true tail of ≈ 0.001) and the √X-error term of Bulk₀ (0.0145).

## 5. CS use (item 5): CONFIRMED (relabel to Lemma 6)

**Where b₄ enters CS.** In CS arXiv:2507.15184v2, `InghamPostArXiv.tex` l.644–669 = **Lemma 6** (`lem:fxone`). The ref text agrees ("Lemma 6. Let T > 0, X ≥ X₀ ≥ 3·10¹⁰, and 0 < δ ≤ (1/20)log X"). b₄ enters through

  Σ_n λ_X(n)²/n^τ ≤ ζ(τ)Σ_{d₁,d₂≤X} μ(d₁)μ(d₂)/[d₁,d₂]^τ ≤ b₄e^{γ(τ−1)}/(τ−1),

which is used at τ = 2σ−1 and τ = σ, with σ = 1+δ/log X.
- The middle quantity is **exactly ζ(τ)·S_{τ−1}(X)** with the same normalisation (lcm, d₁, d₂ ≤ X, exponent 1+ε). The first inequality holds because λ_X(n) = 0 for 1 ≤ n ≤ X and λ_X(n) = −Σ_{d|n, d≤X} μ(d) otherwise, so the left side is at most the full sum Σ_n(Σ_{d|n,d≤X}μ(d))²n^{−τ} = ζ(τ)S_{τ−1}(X).
- The last step also uses ζ(τ) ≤ e^{γ(τ−1)}/(τ−1), which is refereed.
- So CS needs S_ε(X) ≤ b₄ for all X ≥ X₀ and ε ∈ {δ/log X, 2δ/log X}.

**Coverage.**
- CS's own hypothesis (X₀ ≥ 3·10¹⁰, τ ≤ 11/10) is **not** covered by Theorem R. It is covered only when X₀ ≥ 3·10¹².
- The project enforces this: `phase1_cs/cs_bounds.py` `b4_value` raises an error unless T₀ ≥ 3·10¹² and 2δ/log T₀ ≤ 0.0227.
- (A) uses h = 1 (X = T, `A_row`); (B) uses k = 1 (X = kT, `KLN(T0, …)`). In both cases X ≥ T ≥ T₀ ≥ 3·10¹², and ε ≤ 2δ/log X ≤ 2δ/log T₀ ≤ 2·0.3255/log(3·10¹²) = 0.02266 < 0.0227.
- Rows with larger T₀ (e^30, e^32, e^35) are checked the same way.
- b₄ enters only through C₃ and C₄ of CS Lemma 6 (`cs_kln.C5C6`, `cs_thm1.C3f/C4f`); the 3/2-line uses do not involve b₄.

## 6. Deliverables and re-run

| file | content | time |
|---|---|---|
| `REVIEW.md` | this report | |
| `sanity_Seps.py` → `sanity_Seps_1e7_out.txt`, `sanity_Seps_10000000.json` | S_ε(N) for all N ≤ 10⁷, 6 values of ε | 5 min |
| `pieces_check.py` → `pieces_check_1e6_out.txt`, `pieces_check_3e6_out.txt` | every proof inequality at X = 10⁶ + ½ and 3·10⁶ + ½ | 22 s, 30 s |
| `consts_check.py` → `consts_check_out.txt`, `.json` | W, W^h, P, G, S₁₁, S₁₂ (brute force), σ/Σ/Ξ scans to 10⁷, Tail₀/Bulk₀/Bulk₁ | 35 s |
| `F_grid.py` → `F_grid_out.txt` | float re-implementation of (R.10) from the REPORT text; dense grid; robustness variants | 31 s |
| `TN_H2_check.py` → `TN_H2_check_out.txt` | T_N and H₂′ (mpmath) | 2 s |
| `rerun/` | copy of `audit_rza/` with both `--full` re-runs (`run_all_full_output.txt`, `parent_run_all_full_output.txt`, `repair_bound_after_parent_rerun.txt`; `cached_out_before/` holds the original JSONs for comparison) | 27 min + 17 min |

Run everything with `python -I <script> [args as above]` from `work/review_b4/` (python-flint 0.9.0, numpy, mpmath).

All my own scripts use floats and are sanity checks only. They support the verdicts, but no bound is claimed from them. Every claimed bound comes from the repair's Arb certificate, which I re-ran (§3, §7).

## 7. Re-run of the parent audit

`python -I run_all.py --full` was run in `rerun/audit_rza/`.
- Result: **DONE, 0 FAIL**, 16 min 39 s on a machine shared with other jobs; scan A to 4·10⁹ took 590 s.
- All regenerated `out/*.json` files are **byte-identical** to the cached ones: Euler products, scans A, BCD, EF, GHI, and the thm11 sums.
- `repair_bound.py` on the regenerated inputs (`rerun/repair_bound_after_parent_rerun.txt`) gives:
  - rza, X ≥ 3·10¹², ε ≤ 0.0227: **0.5158778644 → 0.5159**;
  - rza, X ≥ 10¹², ε ≤ 0.04: 0.5246401396 → 0.5247;
  - hf, X ≥ 3·10¹², ε ≤ 0.0227: **0.5160930996 → 0.5161**.

Combined with §3, every computational input of Theorem R has been re-run from scratch in this review (on the copied code), with identical results.
