# Primes between consecutive k-th powers for every k ≥ 70 (and for every k ≥ 74 from refereed inputs only)

**A computer-assisted argument with explicitly listed inputs — interim report for review (v4, 2026-11-06)**

**AI authors: Claude and Codex.** Claude leads the traditional explicit-estimate route and developed this manuscript's arguments and implementation. Codex leads the repository's QRH(7/8) route and contributed topic selection and review to this manuscript. This byline records contributions by AI systems; it does not identify them as human authors or imply endorsement by their providers. Human direction and the historical division of work are detailed below.

*Research, proofs, code and text: Claude (Anthropic, Claude Opus 5.5), working almost autonomously at the direction of the project owner (GitHub: bernkastel299792458). Choice of topic: suggested by Codex (OpenAI). External reviews: Codex (OpenAI) and a separate Claude instance. The project owner has not independently verified the mathematics. See "Authorship and AI involvement" below.*

**Status: not peer-reviewed.** Every statement below is meant to be checked.

**Version history**
- **v1** relied on inputs quoted second-hand from Lee (2026).
- **v2** corrected them against the original sources.
- **v3** incorporated two AI reviews (Codex, Claude; `../review/`).
- **v4** responds to an independent audit (`zfr_audit/`), which found an arithmetic error in the PhD-thesis proof of the Littlewood constant 19.62 on which the earlier k = 67 claim depended:
  - **the k = 67 claim is withdrawn**;
  - the interim results are **k = 70** (high confidence) and **k = 74** (conservative: refereed inputs only).

---

## Abstract

For every integer k ≥ 70 and every n ≥ 1, the interval (n^k, (n+1)^k) contains a prime, provided the explicit inputs listed in §3 hold. If only refereed inputs are used, the same holds for every k ≥ 74. The best previously published result valid for all n is k ≥ 86 (E. S. Lee, Acta Arith. 2026); see §1.1 for a more recent conditional claim.

**Method.** The proof follows the explicit-formula / zero-density framework of Lee and of Cully-Hugill–Johnston, with four changes:
- **(H)** a hybrid zero-density bound that splits the σ-integral between the Kadiri–Lumley–Ng-type estimate (with the Johnston–Yang constants) and Bellotti's log-free estimate;
- **(S)** a smoothed explicit formula with the weight y^M(1−y)^M;
- the rows of Bellotti's log-free table below height e^80;
- **(T)** a self-contained tail argument for log x ≥ 10^8.

**Verification.**
- **Numerics.** Certified in Arb ball arithmetic and recorded in re-checkable certificates.
- **Lean 4 / Mathlib.** The logical bookkeeping is formalised, parametrised by k₀, with instances `main_k70` and `main_k74`. The analytic estimates and the certificates enter as hypotheses (Appendix B).

**Dependencies.**
- **k ≥ 70** uses one non-refereed input: the classical zero-free region with constant **4.896** (Bellotti–Trudgian–Yang, arXiv:2603.21490). Our audit verified its proof after correcting 15 non-fatal issues; it depends only on published results.
- **k ≥ 74** uses only refereed results: Mossinghoff–Trudgian–Yang's 5.558691 and Yang's 21.233, among others.
- Both theorems also rest on the new arguments here (Props. H and S, Lemmas 4–6 and T). These have been examined by two AI reviews, but not yet by a human expert.

**Robustness.** Theorem 1 still holds if 4.896 is weakened to 4.98, or if every C in Bellotti's table is multiplied by 1.1 (§11).

**Contributions.**
1. The exponents 70 and 74; the best published value is 86.
2. The ingredients (H), (S), the low-height Bellotti rows and (T), and Lemma 4 (the smooth explicit formula for C¹ weights with absolutely continuous derivative).
3. A check of every input against its source (§3), including four inputs as quoted by Lee (§3.2).
4. An audit of the zero-free-region constants 4.896 and 19.62 (`zfr_audit/`; §1, Remark 1).
5. Arb certificates with a one-command checker, and a Lean formalisation of the assembly.

---

## Authorship and AI involvement

This work was produced almost entirely by AI systems. We describe the division of labour as precisely as we can, so that readers can weigh the results accordingly.

- **Codex** (OpenAI).
  - Before this project began, helped the project owner survey open problems suited to an AI-driven research attempt.
  - It singled out Legendre-type problems (primes between consecutive powers) as a promising candidate, which is how the topic was chosen.
- **Project owner (human).**
  - Posed the problem: primes between consecutive k-th powers *for every n*.
  - Suggested the overall strategy: an explicit bound for large n, closed by computation for small n.
  - Chose the target k = 67, which Claude had identified from Lee's tables as the likely limit of the method.
  - Set the quality requirements: work from the original papers, rigorous numerics, Lean, a review archive.
  - Noticed that the conclusion hinged on the constants 19.62 and 4.896, and asked for them to be audited independently.
  - Obtained the external reviews, and decided which results to state.
  - **Did not derive, implement or check the mathematics.**
- **Claude** (Anthropic, Claude Opus 5.5, via Claude Code).
  - Literature search and reading; all derivations; all code, computations and certificates; the Lean formalisation; this manuscript and the other documents.
  - Separate Claude sessions carried out the audit in `zfr_audit/` and translated the research conversation.
- **External AI reviews of v2** (`../review/`).
  - Codex (OpenAI) wrote one review, including an independent rigorous re-implementation of δ_H.
  - A separate Claude instance wrote another review with its own scripts.

**Known failure modes.** Misquoted constants, inputs used outside their stated range, and missed hypotheses were the most common errors during the project.
- Each error found is recorded in `../LOG.md`, Appendix C and `../review/response_to_reviews_2026-11-06.md`.
- The k = 67 claim of v1–v3 was stated before its key input (19.62) had been audited, and was withdrawn in v4.
- The full research conversation is in `conversation/`. It contains statements that were later corrected; this manuscript is authoritative.

---

## 1. Statements

**Theorem 1 (high-confidence interim result).** Assume inputs (I1)–(I10) of §3 with zero-free regions **(I5-A)** = (4.896, 21.233, 54.004). Then for every integer k ≥ 70 and every integer n ≥ 1 there is a prime p with n^k < p < (n+1)^k.

**Theorem 2 (conservative interim result).** Assume inputs (I1)–(I10) of §3 with zero-free regions **(I5-B)** = (5.558691, 21.233, 54.004), all refereed. Then the same conclusion holds for every k ≥ 74.

**Remarks.**
1. **Withdrawn claim.** Versions v1–v3 claimed k ≥ 67 using the Littlewood constant 19.62 from A. Yang's PhD thesis (UNSW 2025, Thm 1.2). The audit `zfr_audit/thesis_19.62/REPORT.md` found an arithmetic error in its proof:
   - In Lemma 3.8, p. 59, the constant 1.73 should be 5.93.
   - With this correction, the main-term coefficient reaches about 3.53 on log t ∈ [64, 160], whereas the final step tolerates at most about 3.446.
   - The repaired method gives only about 19.90–20.08 (grid estimates).
   - With a uniform 19.90 or 20.08, our method does not close for k = 67 (δ ≈ 1.02 and 1.14 at L ≈ 4200).
   - This is our reading of the thesis. It has not been confirmed by the author, and we would welcome a correction.

   The k = 67 certificates are kept in `certificates/withdrawn_k67/` as *conditional* certificates (valid if 19.62 holds).
2. **Minimality.** 70 and 74 are the smallest exponents that *this method* certifies with (I5-A) and (I5-B) respectively. For k = 69 and k = 73, at least one rigorously evaluated small L-interval has δ ≥ 1 (§11). This does not show that the statements fail for those k.
3. **Reference value.** With the unproven repaired estimate 20.08 in place of 21.233, the method certifies k = 68 (§11). This is for reference only.
4. **Independence from Lee.** The proofs do not use Lee's Propositions 3.2 or 3.3, nor the constants of Lee's eq. (2.7) (§3.2).

### 1.1 Context: results for all n, and a recent claim (as of 2026-11-06)

| Result | k | Status |
|---|---|---|
| Dudek (2016); Mattner (2017); Cully-Hugill (2023); Cully-Hugill–Johnston I (2023) | 5·10⁹; 1 438 989; 155; 140 | published / thesis |
| Cully-Hugill–Johnston II, Funct. Approx. 73 (2025) | 90 | published |
| E. S. Lee, Acta Arith. 225 (2026) 149–162, online 1 Oct 2026, doi:10.4064/aa260304-20-7 | **86** | published. Our source check found issues in some quoted inputs (§3.2); we did not assess whether they affect k = 86. |
| **This work** (Theorem 1 / Theorem 2) | **70 / 74** | not peer-reviewed |
| OpenAI, *The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8* (OpenAI Math Release preprint, dated 30 Sep 2026) | — | **claim**, not peer-reviewed. The release README states that unformalised results "could have issues". |
| M. Visser, *Primes between 8th powers?*, arXiv:2610.20058 (14 Oct 2026) | **8** | **conditional**: "contingent on the validity of the claimed 7/8 version of the QRH" |
| Chamberland–Straub, arXiv:2602.22502 | exponent ≥ 2.25 (real x ≥ 1) | assuming the full Riemann Hypothesis |

If the 7/8 zero-free half-plane is established, Visser's argument gives k = 8 unconditionally, and k = 70 / 74 are no longer records. Our results would then remain of interest only because they use a different set of inputs: classical explicit estimates, and no quasi-RH. We take no position on the correctness of the quasi-RH claim.

## 2. Notation and conventions

- p denotes a prime and Λ the von Mangoldt function.
- θ(x) = Σ_{p≤x} log p, ψ(x) = Σ_{n≤x} Λ(n), ψ₁(x) = ∫₀^x ψ = Σ_{n≤x}(x−n)Λ(n).
- ρ = β + iγ runs over the non-trivial zeros of ζ.
- k₀ ∈ {70, 74} is the exponent being certified.
- L = log x, h = k₀x^{1−1/k₀}, ε = h/x = k₀e^{−L/k₀}.
- H_R = 3 000 175 332 800.

**Inequality (3.2)_{k₀}:** θ(x + h) − θ(x) > 0.

**Counting conventions.** As in the sources, N(T) = #{ρ : 0 < γ < T} and N(σ,T) = #{ρ : 0 < γ < T, β > σ}.

1. **Proposition S.** Zeros enter only through ∫Φ₀ d(−g), where −dg is absolutely continuous. Values of Φ₀ at the countably many ordinates do not affect the integral, so strict counts may be used.
2. **Proposition H and Lemma T.** Choose T⁺ > 2T such that (2T, T⁺] contains no ordinate, and apply each input at height T⁺. Every bound is continuous in the height, so we may let T⁺ ↓ 2T. The certificates support this:
   - the Bellotti row containment is checked with a strict margin, log 2T + 2⁻⁴⁰ ≤ log T₁;
   - the zero-free width is evaluated at height e^{log 2T + 2⁻⁴⁰}.

Zero-free regions are used only in the open form "no zeros with β > 1 − η".

## 3. Inputs

### 3.1 Statements as used, with verification status

Details: `input_verification/report_*.md` (sources), `zfr_audit/` (zero-free regions), `../review/` (external reviews).

| ID | Statement used | Source | Status |
|---|---|---|---|
| (I1) | All zeros with 0 < γ ≤ H_R have β = 1/2. | Platt–Trudgian, Bull. LMS 53 (2021), Thm 1 | CONFIRMED |
| (I2) | N(T) ≤ T log T/(2π) for T ≥ H_R. | Bellotti–Wong, Math. Comp. (2025), Thm 1.1 | CONFIRMED |
| (I3) | For σ ∈ [0.98, 1), T ≥ H_R: N(σ,T) ≤ 17.418(log T)^{5−2σ}T^{8(1−σ)/3} + 2.231(log T)². | Johnston–Yang, JMAA 527 (2023), Lemma 2.6, Table 3 (conservative a₁ = 0.77) | CONFIRMED (both reviews concur) |
| (I4) | For each row (T₀, T₁, α₀, C, B) of Bellotti's Table 2 (Appendix A): N(σ,T) ≤ CT^{B(1−σ)} for T ∈ (T₀, T₁], σ ∈ [α₀, 1]. | Bellotti, J. Number Theory 269 (2025), Thm 1.1; arXiv:2405.12545v2 | CONFIRMED against arXiv v2; **the printed JNT table has not been compared** |
| (I5-A) | For t ≥ 3, ζ(σ+it) ≠ 0 for σ > 1 − 1/(4.896 log t), for σ > 1 − log log t/(21.233 log t), and for σ > 1 − 1/(54.004(log t)^{2/3}(log log t)^{1/3}). | 4.896: Bellotti–Trudgian–Yang, arXiv:2603.21490, Thm 1. 21.233: Yang, JMAA 534 (2024). 54.004: Bellotti, JMAA 536 (2024) (the journal states 53.989). | 4.896: arXiv only; **independently audited** (`zfr_audit/bty_4.896/`; 15 non-fatal issues; closes up to log t ≤ 78.16, 76.47 needed). 21.233 and 54.004: refereed. |
| (I5-B) | As (I5-A) with classical constant 5.558691 (\|t\| ≥ 2). | Mossinghoff–Trudgian–Yang, Res. Number Theory 10 (2024), Thm 1.3 | all refereed |
| (I6) | For x ≥ e^{1000} and max{51, (log x)²} < T < (x^{1/10}−2)/4, there is a T\* ∈ [T, 2T], common to x and x+h, with \|ψ(x+h) − ψ(x) − h + Σ_{\|γ\|≤T\*}((x+h)^ρ − x^ρ)/ρ\| ≤ 1.26[(x+h)(log(x+h))^{4/5} + x(log x)^{4/5}]/T. | Cully-Hugill–Johnston, Funct. Approx. 73 (2025), Thm 1.3, Cor. 3.3, Table 1 | CONFIRMED (both reviews concur) |
| (I7) | For log x ≥ 300: 0.999x^{1/2} + 0.885x^{1/3} < ψ(x) − θ(x) < α₁x^{1/2} + α₂x^{1/3}, where α₁ = 1 + 1.93378·10⁻⁸ and α₂ = 1 + 1.936·10⁻⁸. | Broadbent–Kadiri–Lumley–Ng–Wilk, Math. Comp. 90 (2021), Cor. 5.1, Table 14 | CONFIRMED |
| (I8) | For (Δ, x₀) ∈ {(3.90970·10⁷, 4·10^18), (2.51949·10^11, e^600)} and all y ≥ x₀, the interval (y(1−1/Δ), y] contains a prime. | Cully-Hugill–Lee, Math. Comp. 91 (2022) + Corrigendum 93 (2024); arXiv:2103.05986v3 | CONFIRMED against arXiv v3; upstream dependency: see (I10) |
| (I9) | Smooth explicit formula (Lemma 4). | Classical; full proof in §7 via ψ₁ (Ingham 1932, Ch. IV) | proof given |
| (I10) | The upstream inputs of (I8): KLN Lemma 3.2 rests on (a) \|ζ(1/2+it)\| ≤ 0.63t^{1/6}log t for t ≥ 3, and (b) max_{\|t\|≤T}\|ζ(1/2+it)\| ≤ 0.63T^{1/6}log T + 2.851 for all T > 0. | (a) Hiary–Patel–Yang, J. Number Theory 256 (2024), Thm 1.1: 0.618 (it "restores the 0.63 constant and improves it"). (b) The small-T case. | (a) CONFIRMED. (b) **Verified in Arb**: max_{[0,3]}\|ζ(1/2+it)\| ≤ 1.4604150 < 2.851 − 6·0.63/e = 1.4604157 (`code/kln_lemma32_check.py`; point raised by the Claude review). |

**Withdrawn input.**
- (I5-thesis / I5-LW) used the Littlewood constant 19.62 (Yang thesis, Thm 1.2). Its proof contains the arithmetic error described in §1, Remark 1, and is therefore no longer used.
- The audit also found that the thesis constants 4.862 and 19.62 depend on each other circularly. This can be repaired via 4.896.

### 3.2 Notes on inputs quoted by Lee (2026) (not used here)

1. **Lee eq. (2.7)** quotes 17.253 / 5.663 for all 0.6 < σ < 1.
   - These values come from KLN's grid table, which stops at σ = 0.99 and uses an older RH height; σ ∈ (0.99, 1) is not directly covered.
   - (v2's attribution of the problem to Hiary's bound was inaccurate: HPY restored that bound.)
   - We use the conservative values (I3) of Johnston–Yang instead.
2. **Lee eq. (3.3)** misquotes the lower T-condition of CHJ II. We check the original condition, T > max{51, log² x}.
3. **Lee Prop. 3.3:** a displayed inequality in the proof is false. We derive the lower range directly from (I8) (Lemma 6).
4. **Lee Prop. 3.2:** no monotonicity argument is given. It is replaced by Lemma T.

## 4. Reduction (Lean: `main_of_gap`, `exists_prime_of_theta_sub_pos`)

**Lemma 1.** Let k₀ ≥ 62. If for every real x ≥ 4·10^18 some prime p satisfies x < p ≤ x + k₀x^{1−1/k₀}, then for every k ≥ k₀ and n ≥ 1 the interval (n^k, (n+1)^k) contains a prime.

*Proof.*
- For n = 1, take p = 2.
- For n ≥ 2, put x = n^k. Then x ≥ 2^{k₀} ≥ 2^62 > 4·10^18.
- Since k(1 − 1/k₀) ≤ k − 1, we have k₀x^{1−1/k₀} ≤ k n^{k−1}.
- Also n^k + k n^{k−1} + 1 ≤ (n+1)^k. ∎

**Lemma 2.** If θ(y) − θ(x) > 0, then some prime p satisfies x < p ≤ y.

## 5. Lower range (Lean: `ineq32_of_CHL`, `ineq32_of_CHL_range`)

**Lemma 6.** Let Δ > 1, and let (I8) hold for (Δ, x₀). If x ≥ x₀ and k₀x^{−1/k₀}(Δ−1) ≥ 1, then (3.2)_{k₀} holds at x.

*Proof.* With y = x + h, the interval (y(1−1/Δ), y] lies inside (x, x+h]. ∎

**Corollary.** (3.2)_{k₀} holds for 4·10^18 ≤ x with log x ≤ L₁(k₀), where L₁(70) = 2186309/1024 ≈ 2135.07 and L₁(74) = 578863/256 ≈ 2261.18. It suffices that
- exp(600/k₀) ≤ k₀(Δ₁−1), and
- exp(L₁/k₀) ≤ k₀(Δ₂−1).

Both are checked in Arb (`code/numeric_facts.py`). The margins are 2.7·10⁹ and 4.4·10⁸ for k₀ = 70, and 2.9·10⁹ and 4.2·10⁸ for k₀ = 74.

## 6. Proposition H (sharp truncation, hybrid density)

Let k ≥ 11, x ≥ e^{1000}, L = log x, μ ∈ (1/k, 1/10), 2T = x^μ, and u = μL. Assume:

- **(H1)** T ≥ H_R and max{51, L²} < T < (x^{1/10} − 2)/4.
- **(H2)** ζ(σ+it) ≠ 0 for σ > 1 − η and |t| ≤ T⁺, for all T⁺ in some interval (2T, 2T(1+τ)].
- **(H3)** 0.98 ≤ σ₁ ≤ σ\* < 1. Some row of (I4) satisfies log T₀ ≤ u, u + τ′ ≤ log T₁ for some τ′ > 0, and α₀ ≤ σ\*.
- **(H4)** λ_K := L(1 − 8μ/3) − 2 log u ≥ 1, and λ_B := L(1 − Bμ) ≥ 1.

Then |θ(x+h) − θ(x) − h| ≤ δ_H h, where δ_H = E_triv + E_K + E_B + E_tr + E_pp with

- E_triv = (u/π)e^{−(1−σ₁−μ)L},
- E_K = 2·17.418u³(L/λ_K)e^{−(1−σ\*)λ_K} + 2·2.231u²e^{−(1−σ\*)L},
- E_B = 2C(L/λ_B)e^{−ηλ_B},
- E_tr = (2·1.26/k)[(1+ε)(L+ε)^{4/5} + L^{4/5}]e^{−(μ−1/k)L},
- E_pp = k⁻¹(α₁√(1+ε) − 0.999)e^{−(1/2−1/k)L} + k⁻¹(α₂(1+ε)^{1/3} − 0.885)e^{−(2/3−1/k)L}.

**KLN-only variant.** E_K + E_B is replaced by 2·17.418u³(L/λ_K)e^{−ηλ_K} + 2·2.231u²e^{−ηL}.

*Proof.*
1. **Truncated explicit formula.** By (I6), |ψ(x+h) − ψ(x) − h| ≤ |Σ(T\*)| + hE_tr.
2. **Prime powers.** By (I7), 0 ≤ (ψ−θ)(x+h) − (ψ−θ)(x) ≤ hE_pp.
3. **Zero sum.** Since |((x+h)^ρ − x^ρ)/ρ| ≤ hx^{β−1} and ρ ↔ ρ̄ is a symmetry, |Σ(T\*)| ≤ 2hΣ_{0<γ<T⁺}x^{β−1}.
4. **As an integral over σ.** Write x^{β−1} = x^{−1} + ∫₀^β x^{σ−1}L dσ. Then Σ_{0<γ<T⁺}x^{β−1} = x^{−1}N(T⁺) + ∫₀¹ N(σ,T⁺)x^{σ−1}L dσ.
   - On [0, σ₁], bound N(σ,T⁺) ≤ N(T⁺); this gives E_triv via (I2).
   - By (H2), N(σ,T⁺) = 0 for σ > 1 − η.
5. **Splitting the σ-integral.** Split ∫_{σ₁}^{1−η} = ∫_{σ₁}^{σ\*} + ∫_{σ\*}^{1−η}.
   - On [σ₁, σ\*], (I3) together with ∫e^{−(1−σ)λ}dσ ≤ e^{−(1−σ\*)λ}/λ (Lean: `integral_exp_bound`) gives E_K.
   - On [σ\*, 1−η], (I4) gives E_B.
6. **Conclusion.** Let T⁺ ↓ 2T and combine the bounds (Lean: `propH_combination`). ∎

## 7. Proposition S (smoothed explicit formula)

**Setup.**
- Let M ≥ 2 and φ(y) = y^M(1−y)^M on [0,1], with φ = 0 outside. Then φ ∈ C^{M−1}, φ^{(M−1)} is Lipschitz, and φ^{(M)} is bounded and piecewise polynomial.
- Let F(t) = φ((t−x)/h), and R_j = ‖φ^{(j)}‖₁/∫φ with upper bounds R̃_j ≥ R_j.
- Let g(t) = min{1, min_{1≤j≤M} R̃_j(1+ε)^j(x/(ht))^j}. Then g is continuous, non-increasing and piecewise C¹.

**Lemma 3.** |F̂(ρ)| ≤ h∫φ·x^{β−1}g(|γ|), where F̂(s) = ∫F(t)t^{s−1}dt.

*Proof.*
- Directly, |F̂(ρ)| ≤ x^{β−1}h∫φ.
- For j ≤ M, integrate by parts j times. This is valid because φ^{(i)} is absolutely continuous for i ≤ M−1, and there are no boundary terms because φ^{(i)}(0) = φ^{(i)}(1) = 0.
- Finally use ∫|F^{(j)}| = h^{1−j}‖φ^{(j)}‖₁, |ρ+i| ≥ |γ|, and (x+h)^{β+j−1} ≤ x^{β−1}x^j(1+ε)^j. ∎

**Lemma 4 (I9).** Let F have compact support in (1,∞), with F ∈ C¹, F′ absolutely continuous and F″ ∈ L¹. Then

Σ_n Λ(n)F(n) = ∫F − Σ_ρ F̂(ρ) − ∫F(t)dt/(t³−t),

with Σ_ρ|F̂(ρ)| < ∞. This covers φ_M for all M ≥ 2, including M = 2, where φ is only C¹.

*Proof.*
1. **The formula for ψ₁.** For x ≥ 1,
   ψ₁(x) = x²/2 − Σ_ρ x^{ρ+1}/(ρ(ρ+1)) − xζ′(0)/ζ(0) + ζ′(−1)/ζ(−1) − Σ_{r≥1}x^{1−2r}/(2r(2r−1)),
   and the ρ-series converges absolutely and uniformly on compact sets (Ingham 1932, Ch. IV).
2. **Integration by parts.** Since ψ₁ is absolutely continuous with ψ₁′ = ψ a.e., Σ_nΛ(n)F(n) = −∫F′ψ = −∫F′dψ₁ = ∫F″ψ₁.
3. **Termwise integration.** Integrate the formula term by term against F″.
   - By two integrations by parts, ∫F″t^{ρ+1}/(ρ(ρ+1)) = F̂(ρ).
   - ∫F″t²/2 = ∫F, while ∫F″t = ∫F″ = 0.
   - Since (t^{1−2r}/(2r(2r−1)))″ = t^{−2r−1}, the trivial zeros give ∫F/(t³−t).
4. **Convergence.** |F̂(ρ)| ≤ ‖F″‖₁ max t^{β+1}/|γ|². ∎

**Proposition S.** Let x ≥ e^{300}, and let Φ ≥ Φ₀(t) := Σ_{H_R<γ<t}x^{β−1}. Define

δ_S = 2∫Φ d(−g) + 2N(H_R)x^{−1/2} + (‖φ‖_∞/∫φ)(E_pp + 1/(x³−x)).

If δ_S < 1, then Σ_{x<p<x+h}(log p)φ((p−x)/h) > 0.

*Proof.*
- Apply Lemmas 3 and 4, together with (I1) and the symmetry ρ ↔ ρ̄.
- Use Stieltjes integration by parts, ∫g dΦ₀ = ∫Φ₀ d(−g); the boundary terms vanish.
- Bound the trivial-zero term and the prime-power term.
- Combine (Lean: `propS_combination`, `exists_pos_term`). ∎

**Lemma 5 (choice of Φ).** Let t ≥ H_R, v = log t, and η(t) = max{1/(Z₁v), log v/(Z₂v), 1/(Z₃v^{2/3}(log v)^{1/3})}, which is decreasing for t > e^e. Put σ₁ = 0.98. Then each of the following is a valid Φ(t):

- **(a)** t log t/(2π);
- **(b)** (tv/2π)x^{σ₁−1} + 17.418v³(L/λ)e^{−ηλ} + 2.231v²e^{−ηL}, if λ := L − 8v/3 − 2 log v ≥ 1;
- **(c)** for a row of (I4) with log T₀ ≤ v ≤ log T₁ and α₀ ≤ σ\* < 1−η, the quantity
  (tv/2π)x^{σ₁−1} + 17.418v³(L/λ)e^{−(1−σ\*)λ} + 2.231v²e^{−(1−σ\*)L} + C(L/λ_B)e^{−ηλ_B},
  if λ ≥ 1 and λ_B := L − Bv ≥ 1.

## 8. Lemma T (tail, log x ≥ 10^8)

**Lemma T.** For k₀ ∈ {70, 74}, (3.2)_{k₀} holds for all x with L = log x ≥ 10^8.

*Proof.*
- **Setting.** Use the KLN-only variant of Prop. H with μ = 1.01/k₀ and σ₁ = 0.98. Take η = η_VK(e^u) = 1/(Z₃u^{2/3}(log u)^{1/3}) with Z₃ = 54.004; this region is refereed and holds at every height. Put
  - a = 1 − σ₁ − μ,
  - a₂ = 1 − 8μ/3 − 2 log(μL₃)/L₃,
  - b = μ − 1/k₀,
  - w(L) = Lη_VK(e^{μL}).
- **Majorants.** For L ≥ L₃ = 10^8 we have δ_H(L) ≤ U(L) := U_triv + U_K + U_tr + U_pp, where
  - U_triv = (μL/π)e^{−aL},
  - U_K = (2·17.418/a₂)(μL)³e^{−a₂w} + 2·2.231(μL)²e^{−w},
  - U_tr = (2·1.26/k₀)c_trL^{4/5}e^{−bL},
  - U_pp is the corresponding prime-power term.
- **Monotonicity.** Each majorant is non-increasing on [L₃, ∞):
  - for U_triv this follows from aL₃ > 1;
  - for U_tr from bL₃ > 4/5;
  - for U_K from w(1 − 1/log μL) ≥ 9/a₂ at L₃, using that this quantity is non-decreasing once log μL > 1.
- **Hypotheses of Prop. H.** These persist for all L ≥ L₃.
- **Arb checks.** All conditions are checked in Arb (`code/tail.py L₃ k₀`). The results are U(10^8) ≤ 1.05·10⁻⁵ for k₀ = 70 and U(10^8) ≤ 8.2·10⁻⁷ for k₀ = 74. Hence U(L) ≤ U(L₃) < 1. ∎

Lemma T uses no non-refereed input.

## 9. Rigorous computation and certificates

All numerics use Arb ball arithmetic (python-flint 0.9.0). Each certificate is a list of consecutive L-intervals with exact rational endpoints. L is treated as a ball, so every bound holds for *every* L in the interval.

**Proposition H** (`rig_delta`).
- (H1)–(H4) are certified, including the strict row margin.
- η is a certified lower bound at height e^{u_max + 2⁻⁴⁰}.

**Proposition S** (`rig_delta_smooth_pure`).
- **Cells.** On each cell, Lemma 5 gives an Arb upper bound for sup Φ. Rows are decided by certain comparisons, and a cell meeting several rows takes the maximum over them.
- **Abel step.** Σ(S′_i − S′_{i−1})ĝ_i (Lean: `abel_bound`).
- **Start point.** A dyadic point ≤ max(log H_R, the end of the region where g ≡ 1).
- **Tail.** Closed form.
- **R̃_j.** Exact Taylor bounds.
- **Accumulation.** Pure Arb.

**Certificates (generated by `code/make_chain.py`, checked by `code/verify_all.py`).**

| k₀ | Inputs (I5) | S: range, pieces, max δ | H: range, pieces, max δ | Lemma T: U(10^8) |
|---|---|---|---|---|
| **70** | A: 4.896 / 21.233 / 54.004 | [2186309/1024, 9521], 2109, **0.81996** | [9521, 10^8], 1858, **0.85975** | ≤ 1.05·10⁻⁵ |
| **74** | B: 5.558691 / 21.233 / 54.004 | [578863/256, 7343], 2539, **0.93300** | [7343, 10^8], 1911, **0.88492** | ≤ 8.2·10⁻⁷ |

In both chains, each S piece uses whichever of M ∈ {2, 3} gives the smaller bound, and pieces are made finer as δ approaches 1. The S and H ranges were chosen so that H starts well above its own threshold; for k₀ = 70 the H threshold is 8706. The tightest pieces of either method are therefore not needed.

`verify_all.py` does the following:
- re-runs every check in pure Arb;
- asserts the exact endpoints L₁, L₂ and 10^8;
- runs `numeric_facts.py`, `kln_lemma32_check.py` and `tail.py` for each k₀;
- prints SHA256 hashes.

Its output is in `certificates/verify_all_output.txt`.

**Independent re-implementations by the reviews** (of the v2 k = 67 chain; same formulas):
- Codex: δ_H rigorously in Arb.
- Claude: δ_H and δ_S pointwise in mpmath.

## 10. Proofs of Theorems 1 and 2

Let k₀ ∈ {70, 74}, x ≥ 4·10^18 and L = log x. Then (3.2)_{k₀} holds in each range:

- **L ≤ L₁(k₀):** by Lemma 6.
- **L₁ ≤ L ≤ L₂:** by Prop. S and its certificate. Prop. S gives a prime in (x, x+h), hence θ(x+h) − θ(x) > 0.
- **L₂ ≤ L ≤ 10^8:** by Prop. H and its certificate.
- **L ≥ 10^8:** by Lemma T.

Lemmas 1–2 then give the theorems. In Lean, these are `main_k70` and `main_k74`, which take the four ranges and the inputs as fields of `Hypotheses k₀ L₁ L₂ L₃`. ∎

## 11. Minimal k, margins and limits

**Smallest k certified by this method.** For each constant set we ran a rigorous sample scan of the S-window (`code/scan_min_k.py`; best of M ∈ {2,3} at each sample), followed by full certificate chains for the minimal k.

| (I5) classical / Littlewood / VK | Status | Minimal k | Max δ at k−1 (samples) |
|---|---|---|---|
| 4.896 / 21.233 / 54.004 (A) | 4.896 arXiv (audited); rest refereed | **70** | 1.011 (k = 69) |
| 5.558691 / 21.233 / 54.004 (B) | all refereed | **74** | 1.132 (k = 73) |
| 4.896 / 20.08 / 54.004 | 20.08 = repaired-thesis estimate, **unproven** | 68 (reference) | 1.152 (k = 67) |
| 4.896 / 19.62 / 54.004 | 19.62: proof erroneous (§1) | 67 (withdrawn) | — |

**Margins.** The largest certified δ is 0.82 (S) and 0.86 (H) for k₀ = 70, and 0.93 (S) and 0.88 (H) for k₀ = 74.

**Sensitivity to the inputs** (`code/sensitivity.py`, output in `certificates/sensitivity_output.txt`).
- **Method.** Every archived certificate piece is re-evaluated in Arb, with the same endpoints, after changing one input. For S pieces, both M = 2 and M = 3 are tried. A failing piece might still be repaired by re-optimising the chain, so the tolerances found are lower bounds for what the method tolerates.
- **Why Z₁ affects only S.** The classical region is wider than the Littlewood region only where 1/(Z₁ log t) > log log t/(Z₂ log t), that is, for log t < exp(Z₂/Z₁). For Z₁ = 4.896 this means log t < 76.5, and the bound is smaller for larger Z₁. The H-range has log 2T > 137, so H is unaffected by Z₁.

| Change | k₀ = 70: max δ (S / H) | k₀ = 74: max δ (S / H) |
|---|---|---|
| none | 0.820 / 0.860 | 0.933 / 0.885 |
| Z₁ = 4.95 | 0.927 / — | |
| Z₁ = 4.98 (+1.7%) | **0.993** / — | |
| Z₁ = 4.99 | 1.008 (fails) / — | |
| Z₁ = 5.1 | 1.088 (fails) / — | |
| Z₁ = 5.558691 (MTY) | 2.06 (fails) / — | (this is (I5-B)) |
| Bellotti C × 1.05 | 0.861 / 0.902 | 0.980 / 0.928 |
| Bellotti C × 1.1 | **0.902 / 0.944** | 1.026 (fails) / 0.970 |
| Bellotti C × 1.2 | 0.984 / 1.027 (fails) | 1.120 (fails) / 1.056 (fails) |
| Johnston–Yang 17.418, 2.231 × 1.5 | unchanged (E_K < 10⁻³⁸) | unchanged |

**Reading of the table.**
- Theorem 1 tolerates a classical constant up to at least 4.98, 1.7% weaker than 4.896.
  - Separately, the audit found that BTY's final inequality holds with the corrected constants. Its relative margin is 0.05% over the whole range log t ≤ 76.47, and 0.9% for log t ≤ 55.01.
  - So a small numerical error in 4.896 would not affect Theorem 1. Only a substantive flaw in BTY's argument would, and in that case Theorem 2 still applies.
- **Theorem 2 is more sensitive to Bellotti's table than Theorem 1.** "Conservative" refers to the refereed status of its inputs, not to its numerical margin.
- For the earlier k = 67 chain, the Claude review found that C × 1.05 already broke the bound. Comparing the printed JNT table with arXiv v2 therefore remains important for both theorems.

## 12. Items for reviewers

See `REVIEW_CHECKLIST.md`. In order of importance:
1. BTY Theorem 1 (4.896), only for Theorem 1. Our audit is in `zfr_audit/bty_4.896/`.
2. The printed JNT version of Bellotti's Table 2 against arXiv v2.
3. Lemma 4 via ψ₁.
4. Propositions H and S, and Lemmas 5, 6 and T.
5. Code ↔ formulas, and a rigorous second implementation of δ_S.

## Appendix A. Bellotti's Table 2

Source: arXiv:2405.12545v2, Table 2; the last row is from the text, p. 27. The 22 rows with T₁ ≤ e^80 were checked digit by digit against the PDF text and the LaTeX source. All 39 rows were re-checked by the Claude review.

| T₀ | T₁ | α₀ | C | B |
|---|---|---|---|---|
| 3·10^12 | e^29 | 0.9927 | 37341.72 | 14.160 |
| e^29 | e^30 | 0.9927 | 37564.18 | 14.084 |
| e^30 | e^31 | 0.9925 | 40014.59 | 13.588 |
| e^31 | e^32 | 0.9923 | 42840.01 | 13.108 |
| e^32 | e^33 | 0.9921 | 46015.02 | 12.647 |
| e^33 | e^34 | 0.9919 | 49270.71 | 12.226 |
| e^34 | e^35 | 0.9918 | 52249.66 | 11.856 |
| e^35 | e^36 | 0.9916 | 55524.80 | 11.505 |
| e^36 | e^37 | 0.9914 | 59715.72 | 11.134 |
| e^37 | e^38 | 0.9912 | 64228.93 | 10.782 |
| e^38 | e^39 | 0.9910 | 68446.65 | 10.475 |
| e^39 | e^40 | 0.9909 | 71907.32 | 10.217 |
| e^40 | e^41 | 0.9907 | 76267.80 | 9.951 |
| e^41 | e^42 | 0.9906 | 80004.48 | 9.720 |
| e^42 | e^43 | 0.9905 | 83811.09 | 9.501 |
| e^43 | e^44 | 0.9903 | 89209.33 | 9.259 |
| e^44 | e^45 | 0.9901 | 95233.68 | 9.020 |
| e^45 | e^46.2 | 0.9900 | 99227.30 | 8.843 |
| e^46.2 | e^50 | 0.9899 | 104761.04 | 8.634 |
| e^50 | e^60 | 0.9892 | 128806.85 | 7.936 |
| e^60 | e^70 | 0.9876 | 194323.75 | 6.661 |
| e^70 | e^80 | 0.9860 | 278045.07 | 5.809 |
| e^80 | e^90 | 0.9850 | 370655.73 | 5.216 |
| e^90 | e^100 | 0.9850 | 425721.47 | 4.831 |
| e^100 | e^110 | 0.9850 | 488901.14 | 4.513 |
| e^110 | e^120 | 0.9850 | 545744.21 | 4.264 |
| e^120 | e^130 | 0.9850 | 629490.27 | 4.032 |
| e^130 | e^140 | 0.9850 | 694045.43 | 3.855 |
| e^140 | e^150 | 0.9850 | 771373.78 | 3.696 |
| e^150 | e^160 | 0.9850 | 825913.07 | 3.572 |
| e^160 | e^170.2 | 0.9850 | 909966.07 | 3.448 |
| e^170.2 | e^500 | 0.9850 | 1.12·10^6 | 3.337 |
| e^500 | e^1000 | 0.9850 | 6.23·10^6 | 2.152 |
| e^1000 | e^1500 | 0.9850 | 2.12·10^7 | 1.820 |
| e^1500 | e^2000 | 0.9850 | 6.47·10^7 | 1.684 |
| e^2000 | e^2500 | 0.9850 | 1.73·10^8 | 1.610 |
| e^2500 | e^3000 | 0.9850 | 2.56·10^8 | 1.577 |
| e^3000 | e^481958 | 0.9850 | 5.76·10^8 | 1.551 |
| e^481958 | e^{6.7·10^12} | 0.9850 | 1.62·10^11 | 1.448 |

## Appendix B. Lean formalisation (`lean/`; package `LegendreK67`) and its scope

Built with Lean 4.36.0-rc2 and Mathlib v4.36.0-rc2. There is no `sorry`, no `axiom` and no `native_decide`. `#print axioms` lists only `propext`, `Classical.choice` and `Quot.sound`.

| Lean name | Content |
|---|---|
| `key_ineq`, `binom_lower`, `main_of_gap` | Lemma 1 (parameter k₀ ≥ 62) |
| `exists_prime_of_theta_sub_pos`, `theta_sub_pos_of_prime` | Lemma 2 and its converse |
| `CHLInterval`, `ineq32_of_CHL`, `ineq32_of_CHL_range` | Lemma 6 (parameter k₀) |
| `Hypotheses k₀ L₁ L₂ L₃`, `ineq32_all`, `primes_between_consecutive_powers` | assembly of §10 |
| `main_k70`, `main_k74` | the two interim results as instances |
| `abel_bound`, `propH_combination`, `propS_combination`, `exists_pos_term`, `integral_exp_bound` | elementary steps |

**Scope.** The Lean theorems have the form "**if** `Hypotheses k₀ L₁ L₂ L₃` holds, then …". The following are fields of `Hypotheses`, **not proved in Lean**:
- (I8): `CHL1`, `CHL2`;
- the numeric facts: `num1`, `num2`;
- Proposition S plus its certificate: `Hsmooth`;
- Proposition H plus its certificate: `Hhyb`;
- Lemma T: `Htail`.

Also not proved in Lean: (I1)–(I10) themselves and the Arb computations. "No `sorry`" refers to the bookkeeping only.

`zfr_audit/lean/` contains a separate partial formalisation of the BTY argument.

## Appendix C. History of corrections

**v2 (source verification).**
- JY constants replace Lee's (2.7).
- The CHJ T-range is taken from the original.
- The lower range is derived directly from CHL.
- Lemma T is introduced.

**v3 (two AI reviews).**
- Lemma 4 is extended to C¹ functions with F′ absolutely continuous, which covers M = 2.
- The starting point of the smoothed integral is fixed.
- Bellotti-row comparisons are done in Arb.
- Endpoint conventions are fixed.
- λ_K ≥ 1 is stated in Lemma 5.
- The KLN/Hiary history is corrected.
- (I10) is added and verified.
- The context section (§1.1) is added.
- Certificates are regenerated with finer pieces and an S/H overlap.
- The checkers assert endpoints.

**v4 (zero-free-region audit).**
- An error was found in the thesis proof of 19.62, and **k = 67 is withdrawn**.
- New interim results: k = 70 with (I5-A) and k = 74 with (I5-B), each with new certificate chains.
- Lean is generalised to a parameter k₀.

Code bugs found during development are listed in `../LOG.md`.

## Appendix D. External reviews and audit

- **Reviews of v2.**
  - *Codex*: "repairable gaps; no fatal error".
  - *Claude*: "major revision; no mathematical or computational error found; conditional, thin margins".

  All points are addressed (`../review/response_to_reviews_2026-11-06.md`), except the comparison with the printed JNT table, which remains open. The one disagreement: Lee's k = 86 is published, not a preprint.
- **Zero-free-region audit** (`zfr_audit/`).
  - **4.896 (BTY): verified**, with 15 non-fatal issues corrected. Notable ones: a sign error in Lemma 14, a Table 1 entry that is not a valid lower bound, and Lemma 8 used beyond its hypothesis.
  - **19.62 (thesis): cannot be verified.** The Lemma 3.8 arithmetic error is fatal to the constant as stated.

## References

- C. Bellotti, *Explicit bounds for the Riemann zeta function and a new zero-free region*, J. Math. Anal. Appl. 536 (2024) 128249; arXiv:2306.10680.
- C. Bellotti, *An explicit log-free zero density estimate for the Riemann zeta-function*, J. Number Theory 269 (2025) 37–77; arXiv:2405.12545.
- C. Bellotti, T. Trudgian, A. Yang, *Zero-free regions inspired by work of Heath-Brown*, arXiv:2603.21490 (2026).
- C. Bellotti, P.-J. Wong, *Improved estimates for the argument and zero-counting function of the Riemann zeta-function*, Math. Comp. (2025); arXiv:2412.15470.
- S. Broadbent, H. Kadiri, A. Lumley, N. Ng, K. Wilk, *Sharper bounds for the Chebyshev function θ(x)*, Math. Comp. 90 (2021) 2281–2315; arXiv:2002.11068.
- M. Chamberland, A. Straub, *Weakening the Legendre Conjecture*, arXiv:2602.22502 (2026).
- M. Cully-Hugill, *Primes between consecutive powers*, J. Number Theory 247 (2023) 100–117; arXiv:2107.14468.
- M. Cully-Hugill, D. R. Johnston, *On the error term in the explicit formula of Riemann–von Mangoldt* I, Int. J. Number Theory 19 (2023); II, Funct. Approx. Comment. Math. 73 (2025) 223–242; arXiv:2111.10001, arXiv:2402.04272.
- M. Cully-Hugill, E. S. Lee, *Explicit interval estimates for prime numbers*, Math. Comp. 91 (2022) 1955–1970; Corrigendum, Math. Comp. 93 (2024) 1019–1025; arXiv:2103.05986v3.
- A. W. Dudek, *An explicit result for primes between cubes*, Funct. Approx. Comment. Math. 55 (2016) 177–197.
- G. A. Hiary, D. Patel, A. Yang, *An improved explicit estimate for ζ(1/2+it)*, J. Number Theory 256 (2024) 195–217; arXiv:2207.02366.
- A. E. Ingham, *The Distribution of Prime Numbers*, Cambridge (1932).
- D. R. Johnston, A. Yang, *Some explicit estimates for the error term in the prime number theorem*, J. Math. Anal. Appl. 527 (2023) 127460; arXiv:2204.01980.
- H. Kadiri, A. Lumley, N. Ng, *Explicit zero density for the Riemann zeta function*, J. Math. Anal. Appl. 465 (2018) 22–46; arXiv:2101.12263.
- E. S. Lee, *Minimal zero-free regions for results on primes between consecutive perfect kth powers*, Acta Arith. 225 (2026) 149–162, doi:10.4064/aa260304-20-7; arXiv:2602.14340.
- C. Mattner, *Prime numbers in short intervals*, BSc (Honours) thesis, Australian National University (2017).
- M. J. Mossinghoff, T. S. Trudgian, A. Yang, *Explicit zero-free regions for the Riemann zeta-function*, Res. Number Theory 10 (2024) 11; arXiv:2212.06867.
- OpenAI, *The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8*, OpenAI Math Release preprint (dated 30 Sep 2026), github.com/openai/math.
- D. Platt, T. Trudgian, *The Riemann hypothesis is true up to 3·10^12*, Bull. London Math. Soc. 53 (2021) 792–797; arXiv:2004.09765.
- M. Visser, *Primes between 8th powers?*, arXiv:2610.20058 (2026).
- A. Yang, *Explicit bounds on ζ(s) in the critical strip and a zero-free region*, J. Math. Anal. Appl. 534 (2024) 128124; arXiv:2301.03165.
- A. Yang, *Explicit zero-free regions for the Riemann zeta-function*, PhD thesis, UNSW Canberra (2025), doi:10.26190/unsworks/31825 (cited for the withdrawn 19.62).
