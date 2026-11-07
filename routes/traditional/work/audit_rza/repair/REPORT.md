# A repaired bound for S_ε(X) — our own replacement for RZA Theorem 1.2

*Written in `work/audit_rza/repair/`. This is our own lemma. An independent review (`work/review_b4/REVIEW.md`) CONFIRMED all five items, with byte-identical `--full` re-runs. This version includes the review's corrections: the CS lemma number, the E₁⁽²⁾ caveat (now removed), the dropped inputs, and a robustness remark.*

## Result

> **Theorem R.** S_ε(X) ≤ **0.5159** for X ≥ 3·10¹² and 0 < ε ≤ 0.0227.
>
> **Helfgott-free version.** S_ε(X) ≤ **0.5161** for X ≥ 3·10¹² and 0 < ε ≤ 0.0227. This version uses no result from Helfgott's book, neither directly nor through cited papers; see §5–§6.

Here S_ε(X) = Σ_{d,e≤X} μ(d)μ(e)/[d,e]^{1+ε}.

Two further certified values:
- **0.5247** for X ≥ 10¹², 0 < ε ≤ 1/25. This is RZA's own row, where RZA claimed 0.5936.
- 0.5249 for X ≥ 10¹², 0 < ε ≤ 1/25, in the Helfgott-free version.

**What the numbers are.**
- The supremum over ε is reached as ε → 0⁺, so b₄ is essentially our corrected Theorem 1.1 bound for S₀ on X ≥ X₀: 0.5158745 for X₀ = 3·10¹².
- The worst cell of the ε-cover adds 3·10⁻⁶.
- The certified bound decreases to 0.430 at ε = 0.0227.
- Robustness is discussed in §3a.

**For CS Lemma 6** (`lem:fxone`, arXiv:2507.15184v2 `InghamPostArXiv.tex` l.644–669; the same number in v1). It needs S_ε(X) ≤ b₄ for all X ≥ 3·10¹² and ε ≤ 2δ/log X ≤ 2·0.3255/log(3·10¹²) = 0.02266. Theorem R covers this with **b₄ = 0.5159**, or 0.5161 in the Helfgott-free version. Both are smaller than the 0.5936 that our corrected CS rows used.

**Re-run.** `python -I run_all.py` takes about 2 minutes using cached long runs; `python -I run_all.py --full` takes about 30 minutes. Both end with 0 FAIL. See §8.

## 摘要（中文）

- **我们证明了自己的替代引理（Theorem R），并已通过独立审查（五项全部 CONFIRMED）。**
  - 对 X ≥ 3·10¹²、0 < ε ≤ 0.0227，有 S_ε(X) ≤ 0.5159。
  - 完全不用 Helfgott 书稿（直接和间接都不用）的版本给出 S_ε(X) ≤ 0.5161。
  - 这一界供 CS 的 **Lemma 6** 使用。
- **为什么比 RZA 的 0.5936 还好：** 正确的恒等式给出 X^{−ε} 衰减，log X ≥ 28.7 时这一衰减压过了所有与 ε 成比例的代价，所以 ε 上的上确界在 ε → 0 处取到，等于修正后 Theorem 1.1 的 S₀ 界 0.51587。
- **证明结构：**
  - 精确恒等式（RZA 的 (6.6) 在这里出错）；
  - 两个权重估计；
  - ℓ > X/10.9 的部分完全按 RZA 的方式处理（与 G 的抵消是精确的）；
  - ℓ ≤ X/10.9 的交叉项和平方项用权重 (ℓ/X)^{2ε}；
  - 主项：尾部用 (J+1)^{−2ε}，主体用 X^{−ε}h(ℓ)^ε 加 Hölder，因此只需多算一个加权的 Theorem 1.1；
  - 最后在 4013 个 ε 小区间上做 arb 认证。
- **Helfgott 书稿在哪里进入：**
  - 直接进入，只经过 RZA Lemma 2.5（书稿 Lemma 5.10、(5.79)、Lemma 5.17）。它影响尾部 Tail₀ 和 Lemma 3.1 的常数。
  - 替代办法：用我们自己的计算（|m(t)| ≤ √(2/t)、|m₂(t)| ≤ √(3/t) 对 t ≤ 10¹⁰ 成立，已认证），加上 refereed 的 Ramaré 2015 结果 |m(x)| ≤ 0.0144/log x，再推出 H₂′ = 0.029762。
  - 间接进入，原有一处：Zuniga-Alterman 2022 的 E₁⁽²⁾ = 0.232。书稿项 27/70 在其 max 中并不起作用，只需要一个弱形式：sup_{X≥1573}|Q_odd(X)−4X/π²|/√X ≤ 0.2632。
  - 我们证明了这个弱形式：自算到 10⁸ 得 0.0835；X > 10⁸ 用 Cohen–Dress–El Marraki 2007（refereed）。合起来 ≤ 0.0993，于是 E₁⁽²⁾ = 0.23126 不再依赖书稿。
- **鲁棒性：** b₄ = F(0⁺) 与 T₃–T₆ 无关。只要 T₄ 的低估不超过 1.98 倍，上确界就仍在 ε → 0⁺ 处取到（见 §3a）。

## 1. Notation

- b_ℓ = μ²(ℓ)φ(ℓ)/ℓ².
- m_q(Y) = Σ_{n≤Y,(n,q)=1} μ(n)/n, and m_q(Y;s) is the same sum with n^{−s}.
- φ_s(q) = q^s∏_{p|q}(1−p^{−s}).
- P_q(ε) = q^{1+ε}/φ_{1+ε}(q).
- ζ = ζ(1+ε) and G(Y) = Σ_{ℓ≤Y} μ²(ℓ)/φ_{1+ε}(ℓ).
- For Y ≥ 1, Δ_q(Y,ε) is defined by m_q(Y;1+ε) = m_q(Y)Y^{−ε} + P_q(ε)/ζ + εΔ_q(Y,ε)Y^{−ε}, as in RZA Lemma 3.1.
- h(ℓ) = ∏_{p|ℓ} p^{1/(p−1)}.
- Lemma numbers "RZA 4.x" refer to arXiv:2603.25961v3. All their constants are the **audited** values of `../REPORT.md`.

## 2. Statement and inputs

**Theorem R.** Let X₀ = 3·10¹² and ε₀ = 0.0227. For all X ≥ X₀ and 0 < ε ≤ ε₀,

  S_ε(X) ≤ F(ε) ≤ 0.5159,

where F is the explicit function (R.10) below. With X₀ = 10¹² and ε₀ = 1/25 the same proof gives 0.5247.

**Inputs.** Each is listed with its status; "own" means re-computed or proved in this audit.

| # | input | where used | status |
|---|---|---|---|
| A1 | RZA Lemma 3.1: the bound \|Δ_q(Y,ε)\| ≤ 0.03·g₂(q)q^ξ/φ_ξ(q)·1_{Y≥10¹²}/log Y + (4.1g₀(q) + (5+ε2^ε)/2)·(√q/φ_{½}(q))·2^ε/√Y | Steps 4, 5 | IF Thm 1.4 (Math. Comp. 2026, refereed) + RZA Lemma 2.5. Verified in `../lemma31/` |
| A2 | RZA Lemma 3.1 sign table: Δ ≤ 0 for Y < 10.9 (ε ≤ 4/25); Δ ≤ 0 for Y < 47 unless (q, ∏_{p≤43}p) = 1 (ε ≤ 1); lower bound Δ/Y^ε ≥ −P_q/(εζ) for Y < 10.9 | Steps 3, 4 | own Arb certificate (`../lemma31/sign_table_arb.py`, re-run: `out/sign_table_*_rerun.txt`). The lower bound reduces to F₁(x) = Σ_{n≤x,(n,q)=1}μ(n)log(x/n)/n ≥ 0 for x < 10.9, which is Arb-certified for x ≤ 47 and all q (`../lemma31/check_m_values.py`). Ramaré 2015 Cor 1.10 is not needed |
| A3 | m_ℓ(t) patterns: ≥ 0 (t < 5), ≥ −1/30 (t < 10.9), \|m₁\| ≤ 19/210 and m ≥ −2323/30030 (10.9 ≤ t < 47) | Steps 3, 4 | own, exact (`../rza_mpatterns.py`) |
| A4 | \|m_q(t)\| ≤ 1 | Step 4 | Granville–Ramaré, Mathematika 1996, Lem 10.2 (refereed) |
| A5 | RZA Lemma 2.5 (from Lemmas 2.2, 2.3) | A1, Step 7 (Tail₀) | **Helfgott book** (unrefereed) + FA-II (refereed). Replaced in §6 |
| A6 | RZA Lemmas 4.5, 4.6, 4.8, 4.10, 4.11, 4.13 and Cors 4.7, 4.9, 4.12, 4.14 (the last two corrected), with audited constants | Steps 4, 5, 7 | own (Euler products and scans in `../`) on top of Thms 4.1/4.2 of Zuniga-Alterman, Colloq. Math. 2022 (refereed). E₁⁽²⁾ = 0.232 is re-proved without Helfgott's book in Lemma R7 (§5); E₁⁽¹⁾ = 1.044 = Upper(6𝔟₁/π²) does not use Ramaré 2019's 0.43, which is non-binding |
| A7 | RZA Lemma 5.1 (Tail) and the decomposition (5.3) of §5 Part 2 | Step 7 | re-derived (`../REPORT.md` §4) |
| A8 | Lemma 4.3 (Ramaré, Math. Comp. 2016): 1.040 ≤ Σμ²/ℓ − (6/π²)log X ≤ 1.048 for X ≥ 10³ | Step 3 | refereed; our check holds to 10⁸ |
| A9 | 1/ε < ζ(1+ε) | Steps 3, 6 | IF Lem 8.1 (refereed); elementary |
| A11 | exact S₁₁(J), S₁₂(J); W = 0.42824951 | Step 7 | own (`../rza_thm11_ext.py`, `../rza_euler.py`) |
| A12 | h-weighted W^h, P^h, S₁₁^h, S₁₂^h | Step 7 | own (`repair_hweights.py`) |
| A13 | Dusart 2018 (π, θ bounds), for Euler-product tails | everywhere | refereed |

## 3. Proof

**Step 1 (exact identity).** For X ≥ 1 and ε > 0, with Y = X/ℓ,

  (R.1) S_ε(X) = Σ_{ℓ≤X} w_ℓ (m_ℓ(Y) + εΔ_ℓ(Y,ε))² + 2/ζ − G(X)/ζ²,  where w_ℓ = μ²(ℓ)φ_{1+ε}(ℓ)X^{−2ε}/ℓ².

*Proof.*
1. From (d,e)^{1+ε} = Σ_{ℓ|(d,e)} φ_{1+ε}(ℓ) we get S_ε = Σ_ℓ μ²φ_{1+ε}(ℓ)ℓ^{−2−2ε} m_ℓ(Y;1+ε)².
2. Write m_ℓ(Y;1+ε) = n_ℓ + P_ℓ/ζ.
3. The cross terms equal (2/ζ)Σ_ℓ μ²ℓ^{−1−ε}n_ℓ(Y) = (2/ζ)(1 − G(X)/ζ), because Σ_ℓ μ²ℓ^{−1−ε}m_ℓ(X/ℓ;1+ε) = 1 by Möbius inversion. The square terms give G(X)/ζ².
4. Finally, n_ℓ(Y) = Y^{−ε}(m_ℓ(Y) + εΔ_ℓ(Y,ε)), and φ_{1+ε}ℓ^{−2−2ε}·Y^{−2ε} = φ_{1+ε}X^{−2ε}ℓ^{−2}.

(R.1) is checked in Arb at X = 1000 and 3000 (`../rza_counterexample.py`, "corrected identity" column). RZA's (6.6) uses X^{−2ε}b_ℓ in place of w_ℓ. That is smaller by the factor φ_{1+ε}(ℓ)/φ(ℓ) ≥ 1, which is why (6.6) fails (`../REPORT.md` §3).

**Step 2 (Lemma R1, weights).** For squarefree ℓ ≤ X and ε > 0:

- (a) w_ℓ ≤ b_ℓ (ℓ/X)^{2ε};
- (b) w_ℓ ≤ X^{−ε} b_ℓ h(ℓ)^ε (ℓ/X)^ε ≤ X^{−ε} b_ℓ h(ℓ)^ε.

*Proof.* We have φ_{1+ε}(ℓ)/φ(ℓ) = ∏_{p|ℓ}(p^{1+ε}−1)/(p−1).

- For (a): (p^{1+ε}−1) ≤ p^{2ε}(p−1) ⟺ (p^ε−1)(p^ε+1) ≤ (p^ε−1)p^{1+ε} ⟺ 1 ≤ p^ε(p−1), which is true.
- For (b): (p^{1+ε}−1)/(p−1) = p^ε(1 + (1−p^{−ε})/(p−1)) ≤ p^ε(1 + ε log p/(p−1)) ≤ p^ε·p^{ε/(p−1)}. ∎

**Step 3 (ℓ > X/10.9, i.e. Y < 10.9).** By A2, −P_ℓ/ζ ≤ εΔ_ℓY^{−ε} ≤ 0, and w_ℓ = a_ℓY^{−2ε} with a_ℓ = μ²φ_{1+ε}ℓ^{−2−2ε}.

- *Square terms:* ε²w_ℓΔ_ℓ² = a_ℓ(εΔ_ℓY^{−ε})² ≤ a_ℓP_ℓ²/ζ² = μ²(ℓ)/(φ_{1+ε}(ℓ)ζ²). Summed over ℓ > X/10.9, this is (G(X) − G(X/10.9))/ζ².
- *Cross terms:* 2εw_ℓm_ℓΔ_ℓ = 2a_ℓY^{−ε}m_ℓ(εΔ_ℓY^{−ε}).
  - It is ≤ 0 when m_ℓ ≥ 0, which covers Y < 5 by A3.
  - Otherwise −1/30 ≤ m_ℓ < 0 (by A3), and it is ≤ (2/30)a_ℓY^{−ε}P_ℓ/ζ = (2/(30ζ))X^{−ε}μ²(ℓ)/ℓ ≤ (2ε/30)X^{−ε}μ²(ℓ)/ℓ (by A9).
  - Summing over X/10.9 < ℓ ≤ X/5 with A8 (valid since X/10.9 ≥ 10³) gives ≤ 2εX^{−ε}ax₁, where ax₁ = (6π^{−2}log(10.9/5) + 0.008)/30 = 0.0160591.

**Step 4 (cross terms, ℓ ≤ X/10.9).**

*Bounding m_ℓΔ_ℓ.*
- For 10.9 ≤ Y < 47: if the class (ℓ, ∏_{p<47}p) is not 1, then Δ ≤ 0 (A2) and m ≥ −2323/30030 (A3). If the class is 1, then |m| ≤ 19/210 (A3). Either way m_ℓΔ_ℓ ≤ ax₂|Δ_ℓ| with ax₂ = 19/210.
- For Y ≥ 47: m_ℓΔ_ℓ ≤ |Δ_ℓ| by A4.

*Weights.* By R1(a), w_ℓ ≤ b_ℓY^{−2ε}. Writing 1 = ax₂ + (1−ax₂) on ℓ ≤ X/47 and inserting A1:

- The √-part contributes at most 2ε·2^ε(4.1·Ξ₂ + a_ε·Ξ₁)(X/Z)/√X with Z = 10.9 or 47, where a_ε = (5+ε2^ε)/2.
- RZA Lemma 4.10 (audited: Ξ₁ ≤ 2.5879√Y, Ξ₂ ≤ 1.8223√Y) then gives

  T₄ = 2ε·2^ε(4.1·THx + a_ε·THxxx)·[10.9^{−2ε}ax₂/√10.9 + 47^{−2ε}(1−ax₂)/√47].

- The log-part (ℓ ≤ X/10¹²) contributes at most 2ε·0.03·Λ(X,ε), where Λ = Σ_{ℓ≤X/10¹²} b_ℓ g̃(ℓ)(X/ℓ)^{−2ε}/log(X/ℓ) and g̃ = g₂(ℓ)ℓ^ξ/φ_ξ(ℓ).

*Lemma R3.* Λ ≤ (mx−mm)/L₀ + mm/log X + c₁E₁(2εL₀), where L₀ = log 10¹².
- Proof: by partial summation against K₁(t) = Σ_{ℓ≤t} b_ℓ g̃(ℓ) with φ_ε(t) = (X/t)^{−2ε}/log(X/t), which is increasing.
- It uses c₁log t + mm ≤ K₁(t) ≤ c₁log t + mx (RZA Lemma 4.11 with the corrected c₁ ≤ 0.71336, mx = 1.29417, mm = 0.50554 > 0).
- It also uses ∫_1^{X/10¹²} φ_ε dt/t = ∫_{L₀}^{log X} e^{−2εv}dv/v ≤ E₁(2εL₀). ∎

This gives T₅ = 0.03[2ε(mx−mm)/L₀ + 2ε·mm/log X₀ + c₁·uE₁(u)/L₀] with u = 2εL₀. Note that uE₁(u) → 0 as u → 0.

**Step 5 (square terms, ℓ ≤ X/10.9).** By R1(a), w_ℓ ≤ 10.9^{−2ε}b_ℓ. Bohr's inequality (u+v)² ≤ (1+1/c)u² + (1+c)v², together with A1 and RZA Lemma 4.5 (σ₁, σ₂, Σ₁ ≤ THx1, THx2, TH1 times Y) and the corrected Cor 4.14 (Σ_{ℓ≤X/10¹²} b g̃²/log²(X/ℓ) ≤ LL₂ = c₂/L₀ + (log2mx − min(log2mm,0))/L₀² = 0.0622966), gives

  T₆ = ε²·10.9^{−2ε}[(1+1/c)·0.03²·LL₂ + (1+c)·2^{2ε}·(a_ε²THx1 + 8.2a_ε·THx2 + 4.1²·TH1)/10.9].

**Step 6.** Since G ≥ 0 and by A9: 2/ζ − G(X/10.9)/ζ² ≤ 2/ζ < 2ε =: T₇. (The earlier version also used G(10⁸; 1.1) ≥ 9.1. This changes F only at large ε, where it is far below its supremum, so the review dropped it.)

**Step 7 (main term).** Write M = Σ_ℓ w_ℓ m_ℓ(Y)² and D = X/(J+0.9999).

- *Tail, ℓ ≤ D.* By R1(a), the contribution is ≤ (J+0.9999)^{−2ε}S₀**(X,D) ≤ (J+0.9999)^{−2ε}Tail₀. Here Tail₀ = 2TH1/(J+0.9999) + 2√2H₁L₁/√(J+0.9999) + H₁²L₂ is RZA Lemma 5.1 with audited constants.
- *Bulk, ℓ > D.* By R1(b) and Hölder with t = ε/ε₀ (h(ℓ)^ε = (h(ℓ)^{ε₀})^t):

  Σ_{ℓ>D} w_ℓm_ℓ² ≤ X^{−ε}(Σ_{ℓ>D} b_ℓm_ℓ²)^{1−t}(Σ_{ℓ>D} b_ℓh(ℓ)^{ε₀}m_ℓ²)^t ≤ X^{−ε}Bulk₀^{1−t}Bulk₁^t.

*Lemma R5 (weighted bulk).* For a multiplicative weight c ≥ 1 with c(p) = 1 + O(log p/p),

  Σ_{D<ℓ≤X} b_ℓc(ℓ)m_ℓ(X/ℓ)² ≤ W^c(log 2 + S₁₁^c(J)) + (G₁^c(1+√2) + G₂^c·S₁₂^c(J))/√X.

The constants are the same as in RZA §5 Part 2, with f(p) = (p−1)c(p)/p² in place of (p−1)/p². Explicitly:
- W^c = ∏(1+f)(1−1/p);
- r^c_q = ∏_{p|q}(1+f(p))^{−1};
- t^c_q = ∏_{p|q}(1 + (1−|pf−1|)/(√p−1+|pf−1|));
- P^c = ∏(1+|pf−1|/(√p−1));
- G₁^c = w₁^cP^c and G₂^c = E₁⁽²⁾P^c.

*Proof.* Use the decomposition of RZA (5.3) with ℓ = nℓ′, (ℓ′, Π(j)) = 1, and c(ℓ) = c(n)c(ℓ′). Apply Theorem 4.2[A] (α = 1, β = 2−δ) to G^c_q(Y) = Σ_{ℓ≤Y,(ℓ,q)=1} μ²φc/ℓ². Then sum over all n | Π(j), which only increases the bound. ∎

With c ≡ 1 this is Bulk₀, our corrected Theorem 1.1 bulk. With c = h^{ε₀} it is Bulk₁. The tails of W^h and P^h for p > 10⁸ are bounded using c(p) − 1 ≤ 1.000001·ε₀ log p/(p−1), Dusart's C₂ and C_{3/2}, and B_{3/2} (`repair_hweights.py`).

**Step 8 (assembly).** The bound is decreasing in X, so taking X = X₀ in every X-dependent factor gives

  (R.10) S_ε(X) ≤ F(ε) := (J+0.9999)^{−2ε}Tail₀ + X₀^{−ε}Bulk₀(Bulk₁/Bulk₀)^{ε/ε₀} + 2εX₀^{−ε}ax₁ + T₄ + T₅ + T₆ + T₇.

**Step 9 (certification, `repair_bound.py`).**
- (0, ε₀] is covered by 4013 cells: geometric cells from 10⁻⁹ up to ε₀/4000, then 4000 uniform cells.
- On each cell, every factor of F except uE₁(u) is monotone in ε. We evaluate decreasing factors at the left endpoint and increasing ones at the right. For uE₁(u), which increases only up to u ≈ 0.435, the cell bound is u_hi·E₁(u_lo); on the first cell we use uE₁(u) < u log(1+1/u).
- Everything is in Arb with all constants as balls, with J = 68 and c = 0.00205174.

| quantity | value (X₀ = 3·10¹², ε₀ = 0.0227) |
|---|---|
| Tail₀ (J = 68) | 0.0619451190 |
| Bulk₀ | 0.4539294124 |
| Bulk₁ (h^{ε₀}) | 0.4598158619 (λ = log(Bulk₁/Bulk₀)/ε₀ = 0.568) |
| F(0⁺) = Tail₀ + Bulk₀ | 0.5158745314 |
| worst cell [5.7·10⁻⁶, 1.1·10⁻⁵] | **0.5158778655** |
| F at ε₀ | 0.4304 |

So S_ε(X) ≤ 0.5158779 < **0.5159**. ∎

## 3a. Robustness (review item 3)

**The value comes from ε → 0⁺ only.** b₄ = F(0⁺) = Tail₀ + Bulk₀. The terms T₃–T₆ vanish as ε → 0⁺, so they do not enter the value. They only have to keep F(ε) ≤ F(0⁺) for ε > 0.

**Where it is tight.** The tightest point is the far end. At ε₀ = 0.0227 the margin F(0⁺) − F(ε₀) = 0.0855 is about the size of the cross term T₄(ε₀) = 0.0876. The other terms at ε₀ are T₁ = 0.051, T₂ = 0.240, T₃ = 0.0004, T₅ = 0.0002, T₆ = 0.0062 and T₇ = 0.0454.

**Robustness factors** (`repair_margins.py`, point values on a grid of 2040 ε, both variants). κ is the largest factor by which a term could be under-estimated before the supremum would leave ε → 0⁺:

| term | κ (rza) | κ (Helfgott-free) | where binding |
|---|---|---|---|
| T₃ | 177 | 191 | ε → 0 |
| T₄ | **1.975** | **1.980** | ε = ε₀ |
| T₅ | 5.9 | 9.2 | ε → 0 |
| T₆ | 14.8 | 14.9 | ε = ε₀ |
| T₃–T₆ jointly | 1.905 | 1.910 | ε = ε₀ |

So T₄ (Lemma 3.1's √-part, through Ξ₁, Ξ₂ of Lemma 4.10) is the one O(ε) bound whose correctness matters. It was re-derived independently by the review (§2.4 there). If T₄ were under-estimated by a factor κ > 1.98, the bound would not jump catastrophically: it would become about F(ε₀) + (κ−1)·0.088, for example 0.605 at κ = 3.

**Margins of the parameters.**
- A smaller ε₀ increases the margin. The CS use needs only ε ≤ 0.02266.
- The margin also grows with X₀ (X₀^{−ε}).
- The rounding slack of b₄ itself, 0.5159 − F(0⁺) = 2.5·10⁻⁵, is consumed by the ε-cell width near 0 (3·10⁻⁶). It is not consumed by any of T₃–T₆.

**Why this is sharp for the method.** As ε → 0, S_ε(X) → S₀(X), so no bound of this kind can go below sup_{X≥X₀} S₀(X)'s certified bound. Our value is that bound plus 3·10⁻⁶. The decay is fast: d/dε of X₀^{−ε}Bulk₀ is −28.7·0.454 ≈ −13, whereas the cost of the ε-terms is ≈ +2 + 4.5.

## 4. Inputs with numbers (X₀ = 3·10¹², rza variant)

| constant | value |
|---|---|
| TH1, THx1, THx2 (RZA Lemma 4.5) | 2.1205286, 6.2404074, 3.1885613 |
| TH2, TH3 (Lemmas 4.6, 4.8) | 1.9036540, 2.6764484 |
| L₁, L₂ (Cors 4.7, 4.9) | 0.13779107, 0.09686390 |
| THx, THxxx (Lemma 4.10) | 1.8222265, 2.5878076 |
| c₁, mx, mm (Lemma 4.11, corrected) | 0.71335777, 1.2941694, 0.5055381 |
| LL₂ (Cor 4.14 corrected) | 0.06229665 |
| W, G₁, G₂ (Lemma 5.2) | 0.42824951, 2.9682236, 1.1478998 |
| S₁₁(68), S₁₂(68) | 0.3328792894, 21924.0439 |
| W^h, G₁^h, G₂^h, S₁₁^h(68), S₁₂^h(68) | 0.4323580916, 2.8636589, 1.1015508, 0.3357949128, 23491.9569 |
| ax₁, ax₂ | 0.0160591, 19/210 |

## 5. Where Helfgott's book enters

*The book* is H. Helfgott, *The ternary Goldbach problem*, book manuscript, Dec 2019, unrefereed. Source: `../deps_lit/DEPS.md`.

| use | via | enters b₄ through | replaceable? |
|---|---|---|---|
| \|m(t)\| ≤ √(2/t), t ≤ 10¹² (book Lem 5.10) | RZA Lemma 2.2 → 2.5 | Tail₀ (term 2TH1/Z needs g₀ and the √-bound); A1 (the 4.1g₀ term) | **yes**: own certificate to 10¹⁰ (§6) |
| \|m₂(t)\| ≤ √(3/t), t ≤ 10¹² (book (5.79)) | RZA 2.2 → 2.5 (g₀(2) = √3(√2−1)/2) | same | **yes**: own certificate to 10¹⁰ |
| \|m(t)\| ≤ 0.010032/log t (FA-II Cor 1.2, refereed, but it uses book Lem 5.10 on [1.5·10⁷, 10¹⁴]) | RZA 2.3 → 2.5 | Tail₀ (2√2H₁L₁/√Z, H₁²L₂); A1 (log part) | **yes**: Ramaré, Math. Comp. 84 (2015), Thm 1.2, 0.0144/log x for x ≥ 96955 (refereed, 2015, independent of the book) |
| \|m₂(t)\| ≤ 0.0296/log t (book Lem 5.17) | RZA 2.3 → 2.5 (g₂) | same | **yes**: derived H₂′ = 0.029762 from Ramaré 2015 + own certificate (`repair_hf_inputs.py`) |
| sup_{X≥1573}\|Q_odd(X) − 4X/π²\|/√X ≤ 9/70 (book Lem 5.2), used by Zuniga-Alterman 2022 for E₁⁽²⁾ = 0.232 | Theorem 4.2 (Lemma 5.2: G₁ and G₂ both contain E₁⁽²⁾) | Bulk₀, Bulk₁ (≈ 0.0145 of b₄) | **yes, removed** (Lemma R7 below): the book term 27/70 is non-binding in ZA's max, and we prove the weak form it needs |

**Lemma R7 (E₁⁽²⁾ = 0.232 without the book).**

*What ZA does.* In the proof of ZA Lemma `sum2:critic:1` (source `../deps_lit/dl/za22/x/…v3.tex` l.1255–1305; Sage l.566), ZA defines

  E₁⁽²⁾ = (1−1/√2)·max(4𝔟₂/π², 3c_H, 0.40672),  where c_H = sup_{X≥1573}|Q_odd(X) − 4X/π²|/√X.

Here Q_odd counts odd squarefree n ≤ X, and ZA uses c_H ≤ 9/70 (Helfgott's book Lemma 5.2), so 3c_H ≤ 27/70 = 0.386. The term 0.40672 is ZA's own interval computation on [1, 1573]. The max is 4𝔟₂/π² = 0.789570, so E₁⁽²⁾ is unchanged by **any** proved bound c ≥ c_H with 3c ≤ 0.78957.

*Claim.* c_H ≤ c := 0.0993268. Then 3c = 0.29798 < 0.78957, and E₁⁽²⁾ = (1−1/√2)·0.789570 = 0.231260 ≤ 0.232.

*Proof* (`repair_e12.py`).
1. Q_odd(t) = Σ_{k≥0}(−1)^kQ(t/2^k), where Q counts all squarefree numbers, so Q_odd(t) − 4t/π² = Σ_k(−1)^kR(t/2^k) with R(y) = Q(y) − 6y/π².
2. For 1573 ≤ t ≤ 10⁸ we count directly (exact integer counts). The supremum is 0.0834546, attained at t = 2892, which is below Helfgott's 9/70 = 0.1286.
3. For t > 10⁸, let y = t/2^{k₀} ∈ [5·10⁷, 10⁸). The tail Σ_{k≥k₀} equals ±(Q_odd(y) − 4y/π²), which our count bounds by 0.006867√y. For k < k₀ we have t/2^k ≥ 10⁸ ≥ 438653, so by Cohen–Dress–El Marraki (Funct. Approx. 37 (2007), Thm 3 bis, refereed; quoted verbatim as FA-II Lemma `sqf`) |R(t/2^k)| ≤ 0.02767√(t/2^k). Hence |Q_odd(t) − 4t/π²|/√t ≤ 0.02767/(1−2^{−½}) + 2^{−½}·0.006867 = 0.0993268.
4. We also re-checked ZA's 0.40672 on [1, 1573] in Arb (0.40672226, with critical points inside each cell); it is not binding either.

So Theorem 4.2's constants E₁⁽¹⁾ = 1.044 (= Upper(6𝔟₁/π²), with Ramaré 2019's 0.43 non-binding) and E₁⁽²⁾ = 0.232 rest only on refereed results and our own computations. ∎

## 6. Helfgott-free variant (no use of the book at all)

**Lemma R2′.** For every q and X > 0,

  |m_q(X)| ≤ g₀(q)(√q/φ_{½}(q))√(2/X) + H′g₂′(q)(q^{ξ′}/φ_{ξ′}(q))·1_{X≥N}/log X,

with:
- N = 10¹⁰ and ξ′ = 1 − 1/log N;
- H′ = 0.0144 and g₂′(2) = (H₂′/H′)(1−2^{−ξ′}).

*Proof.* As RZA Lemmas 2.4 and 2.5, using:
- (i) |m(t)| ≤ √(2/t) and |m₂(t)| ≤ √(3/t) for t ≤ N — **own certificate** (`repair_mcert.py`: exact Arb for t ≤ 10⁵, parallel segmented sieve with a-priori float error bounds up to 10¹⁰);
- (ii) |m(t)| ≤ 0.0144/log t for t ≥ 96955 — Ramaré 2015;
- (iii) |m₂(t)| ≤ H₂′/log t for t ≥ N, where H₂′ = 0.0144·2.0665108 + 3.5·10⁻⁶ = 0.0297612. This follows from m₂(t) = Σ_k 2^{−k}m(t/2^k), (i), (ii), and the monotonicity of each term in t;
- (iv) the fact that u^{1−ξ′}/log u is increasing for u ≥ N. ∎

**Lemma 3.1′.** The bound of A1 holds with 0.03·1_{Y≥10¹²} replaced by C_log·1_{Y≥N}, where C_log = 2^{ε₀}T_N H′/log 2 = 0.0218353 and T_N = sup_{y≥N}(log y/y)∫_N^y dt/log t = 1.0346374 (Arb cover plus an analytic tail).

*Proof.* IF part 1 (Math. Comp., refereed) gives |Δ| ≤ (2^ε/log 2)X^{−1}∫_1^X|m_q| + (1 + 2^{½+ε}(1+ε2^{ε−1}log 2))√q/(φ_{½}(q)√X). Insert R2′. ∎

**Recomputed with ξ′ and g₂′.** Everything that depends on ξ or g₂ was recomputed (`out_hf/`):
- Euler products;
- the scans for Lemmas 4.6, 4.8 (to 10⁷, 10⁶) and 4.11/4.13 (to 2·10⁸);
- L₁′ = 2TH2′/log N, L₂′ = TH3′/log N, Λ with log N, and LL₂′.

The σ- and Ξ-constants, the sign table and the patterns do not depend on N.

**Result.**

Helfgott-free version (N = 10¹⁰, H′ = 0.0144, H₂′ = 0.029762, C_log = 0.0218353):

| quantity | X₀ = 3·10¹², ε₀ = 0.0227 | X₀ = 10¹², ε₀ = 1/25 |
|---|---|---|
| J, Bohr c | 69, 0.00133 | (optimised) |
| TH2′, TH3′ (Lemma 4.6/4.8 with ξ′, g₂′; maxima at X = 7, 3) | 1.6049261, 1.5706409 | same |
| L₁′, L₂′ | 0.1394021, 0.0682121 | same |
| c₁′, mx′, mm′ (K₁′) | 0.62435411, 1.1724604, 0.5672307 | same |
| LL₂′ | 0.0494549 | same |
| Tail₀′ | 0.0612793852 | — |
| Bulk₀, Bulk₁ | 0.4548117635, 0.4607242651 | — |
| F(0⁺) | 0.5160911486 | 0.5248595711 |
| certified sup | **0.5160931008 → b₄ = 0.5161** | 0.5248670323 → **0.5249** |

So dropping Helfgott's book entirely (Lemma R2′ and Lemma 3.1′ here, Lemma R7 in §5) costs **2.2·10⁻⁴** on b₄ (0.5159 → 0.5161).

**Input status of the Helfgott-free Theorem R (b₄ = 0.5161).**
- Refereed:
  - Zuniga-Alterman 2022 (Thms 3.3/4.6);
  - IF Thm 1.4 and Lem 8.1 (Math. Comp. 2026);
  - Granville–Ramaré 1996;
  - Ramaré 2016 Lem 3.4;
  - Ramaré 2015 Thm 1.2;
  - Cohen–Dress–El Marraki 2007 Thm 3 bis;
  - Dusart 2018.
- The RZA §4–§5 lemmas, re-derived and re-computed in the audit, plus our own lemmas and computations: Theorem R, R1–R7, the sign table, the patterns, all scans and Euler products, and the certificate to 10¹⁰.
- Not used: Helfgott's book, FA-II, Ramaré 2019, or any unaudited RZA statement.

## 7. Caveats for the reviewer

1. **Inputs from the audit.** Steps 3–5 rely on the audited RZA constants (`../REPORT.md` §6). These are our own Arb or float-certified computations, and an independent re-run is advisable for: the σ-scan to 4·10⁹, the K₁/K₂ scans, and the sign table (`--full`).
2. **Uniformity of Theorem 4.2[A].** Lemma R5 uses Theorem 4.2[A] (Zuniga-Alterman 2022, Thm 4.6) for the weighted f. The theorem's constants depend on f only through H, w, t, P as defined, which we computed for each weight. Its hypothesis f(p) = 1/p + O(p^{−β}) with β−α > ½ holds.
3. **Values of X.** RZA Lemma 5.1 and Theorem 4.2 are used for all real X > 0, as stated in the sources.
4. **A1 versus Lemma 3.1′.** The rza variant uses RZA's stated 0.03 (verified). The derivation in Lemma 3.1′ would give 0.0151 at ε₀; this is irrelevant for b₄.
5. **Range in X.** The proof needs X/10.9 ≥ 10³ (for A8). X₀ = 3·10¹² is far above that.
6. **Review simplifications.** These were applied: A10 dropped (T₇ = 2ε), and Ramaré 2015 Cor 1.10 replaced by our own Arb check of F₁ ≥ 0 for x ≤ 47. The certified values are unchanged: 0.5158778655 (rza) and 0.5160931008 (Helfgott-free).

## 8. Files and re-run

| file | content |
|---|---|
| `repair_bound.py` | the certificate (R.10). Variant rza by default; set `RZA_LOG10N=10 RZA_H1=0.0144 RZA_H2=0.029762 RZA_OUTDIR=out_hf` for the Helfgott-free variant |
| `repair_hweights.py` | W^h, P^h, G^h, S₁₁^h, S₁₂^h for a given ε₀ (ε₀ = 0 reproduces the unweighted values) |
| `repair_mcert.py` | own \|m\|, \|m₂\| √-certificate to 10¹⁰ |
| `repair_hf_inputs.py` | H₂′ and T_N |
| `repair_e12.py` | Lemma R7: E₁⁽²⁾ without the book (own odd-squarefree count to 10⁸ + CDE 2007) |
| `repair_margins.py` | robustness factors κ (§3a) |
| `run_all.py` | everything; `--full` also redoes the long computations |
| `out/`, `out_hf/` | outputs; `out/b4_results.json` = summary |

Changes made to shared code in `../`: `rza_common.py` reads the switch threshold N, H₁, H₂ and the output folder from environment variables. The defaults equal the paper's, so `../run_all.py` reproduces earlier outputs unchanged. `rza_assembly.py`, `rza_audited.py`, `rza_scans.py` and `rza_euler.py` use these settings.
