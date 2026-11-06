# Primes between consecutive k-th powers for every k ≥ 70: an AI-generated, computer-assisted interim result

> [!IMPORTANT]
> - **Not peer-reviewed.** This is an interim report, published so that it can be checked.
> - **Conditional on listed inputs.** The theorems hold *if* the published (and, for k ≥ 70, one preprint) estimates listed below are correct. Each input is listed with its status.
> - **AI-generated.** The research, the code, the proofs and this text were produced almost entirely by AI systems. The project owner has not independently checked the mathematics. See [AI involvement](#ai-involvement).
> - **An earlier claim (k ≥ 67) was withdrawn.** It rested on a constant whose proof turned out to contain an error. See [History](#history).

## Abstract

We give a computer-assisted argument that, for every integer **k ≥ 70** and every integer n ≥ 1, the open interval (n^k, (n+1)^k) contains a prime.
- The argument uses exactly one input that has not been refereed: the classical zero-free-region constant 4.896 of Bellotti–Trudgian–Yang (arXiv:2603.21490). We audited its proof independently.
- If only refereed inputs are allowed, the same method gives every **k ≥ 74**.
- The best previously published result valid for all n is k ≥ 86 (E. S. Lee, *Acta Arith.* 225 (2026)).

**Method.** We work within the explicit-formula / zero-density framework of Lee and of Cully-Hugill–Johnston, and add four ingredients:
- **(H)** a hybrid zero-density bound that splits the σ-integral between a Kadiri–Lumley–Ng-type estimate (with Johnston–Yang constants) and Bellotti's log-free estimate;
- **(S)** a smoothed explicit formula with weight y^M(1−y)^M. It comes with a proof of the smooth explicit formula for C¹ weights with absolutely continuous derivative;
- the rows of Bellotti's log-free table below height e^80;
- **(T)** a self-contained tail lemma for log x ≥ 10^8.

**Verification.**
- All numerical inequalities are certified with Arb ball arithmetic and stored as re-checkable certificates. One command, `verify_all.py`, re-checks everything in about 15 minutes.
- The logical assembly is formalised in Lean 4 / Mathlib. The analytic inputs and the certificates enter the Lean proof as explicit hypotheses.

## Main results

| | Statement | Inputs from the literature | Largest certified δ (S / H) |
|---|---|---|---|
| **Theorem 1 (high confidence)** | For all k ≥ **70** and n ≥ 1, (n^k, (n+1)^k) contains a prime. | Zero-free constants 4.896 / 21.233 / 54.004. 4.896 is an arXiv preprint (audited here); everything else is refereed. | 0.820 / 0.860 (δ < 1 is needed) |
| **Theorem 2 (conservative)** | The same for all k ≥ **74**. | Zero-free constants 5.558691 / 21.233 / 54.004; all inputs refereed. | 0.933 / 0.885 |

- **"Conservative"** refers only to the status of the *literature inputs*. Both theorems also rest on the new arguments of this project (Props. H and S, Lemmas 4–6 and T), which have been checked by two AI reviews but not yet by a human expert.
- **Minimality.** 70 and 74 are the smallest exponents *this method* certifies with these inputs. For k = 69 (resp. 73), some rigorously evaluated interval has δ ≥ 1. This says nothing about whether the statement fails for those k.
- **Robustness of Theorem 1.** It survives the following changes; the details are in manuscript §11 and the full output in [`proof/certificates/sensitivity_output.txt`](proof/certificates/sensitivity_output.txt).

  | Input changed | Result |
  |---|---|
  | classical constant 4.896 raised to 4.98 (+1.7%) | still closes |
  | all C in Bellotti's table × 1.1 | still closes |
  | Johnston–Yang constants × 1.5 | no visible effect (that term is below 10⁻³⁸) |

  Theorem 2 still closes with Bellotti's C × 1.05, but fails at × 1.1.

## Core contributions

1. **New explicit exponents.** k ≥ 70 (with one audited preprint input) and k ≥ 74 (refereed inputs only), compared with the published k ≥ 86 (Lee 2026) and k ≥ 90 (Cully-Hugill–Johnston 2025).
2. **Method.** The four ingredients (H), (S), the low-height Bellotti rows and (T) above. They are described in [`proof/manuscript.md`](proof/manuscript.md) §§6–8.
3. **Source verification of the inputs.** Every input was checked against the original papers ([`proof/input_verification/`](proof/input_verification/)). For four inputs as quoted in Lee (2026), the quoted form differs from the source or lacks an argument (manuscript §3.2). We avoid all four. **We have not assessed whether they affect Lee's k = 86.**
4. **Audit of the zero-free-region constants** ([`proof/zfr_audit/`](proof/zfr_audit/)).
   - **4.896 (Bellotti–Trudgian–Yang, arXiv).** Verified after correcting 15 issues, none fatal.
   - **19.62 (Littlewood-type constant, A. Yang, PhD thesis, UNSW 2025).** We believe the proof as written contains an arithmetic slip (Lemma 3.8, p. 59). With it corrected, the same method appears to give only about 19.90–20.08. These are grid estimates, not proofs.

   These are our readings of other authors' work. We would be glad to be corrected.
5. **Reproducibility.** Certificates, checkers, a one-command verification, a Lean formalisation of the bookkeeping, two external AI reviews with our point-by-point response, and the full research conversation.

## What is *not* claimed

- Nothing about Legendre's conjecture itself (k = 2), or about cubes.
- No independent human verification. The project owner directed the work but did not check the proofs (see below).
- Lean does **not** verify the analytic number theory. It verifies that the four ranges and the listed hypotheses together imply the theorem (manuscript Appendix B).
- No position on OpenAI's claimed quasi-Riemann hypothesis (zero-free half-plane Re s > 7/8, preprint, Sep 2026). That claim is not peer-reviewed. M. Visser (arXiv:2610.20058) shows that it would imply the result for k = 8. If the claim is correct, it supersedes the exponents here. Our argument does not use it.

## AI involvement

This project is an experiment in **almost fully autonomous AI research**. We state the division of labour as precisely as we can.

| Who | What |
|---|---|
| **Codex** (OpenAI) | Before this project began, helped the project owner survey open problems suited to an AI-driven research attempt. It singled out Legendre-type problems (primes between consecutive powers) as a promising candidate. This is how the topic was chosen. |
| **Project owner** ([@bernkastel299792458](https://github.com/bernkastel299792458)) | Posed the question (for which k can one prove a prime between consecutive k-th powers *for all n*?). Suggested the overall strategy: an explicit analytic bound for large n, closed by computation for small n. Chose the target k = 67, which Claude had identified from Lee's tables as the likely limit of the method. Set the quality requirements: work from the papers, rigorous numerics, Lean, an archive for review. Pointed out that the results hinged on the constants 19.62 and 4.896 and asked for them to be audited independently. Obtained two external AI reviews. Chose which results to state. **Did not write the mathematics or the code, and did not verify them.** |
| **Claude** (Anthropic, Claude Opus 5.5, via Claude Code) | Found and read the literature. Did all derivations (Props. H and S, Lemma 4, Lemma T) and wrote all verification code, the certificates, the Lean formalisation, the manuscript and the documentation. Further Claude sessions carried out the independent audit of 4.896 / 19.62 (`proof/zfr_audit/`) and translated the conversation. |
| **Codex** (OpenAI), as reviewer | One review of manuscript v2, including an independent rigorous re-implementation of δ_H, and a note on the quasi-RH claim. The files are named `review/GPT_*.md`. |
| **Claude, separate instance** | One independent review of manuscript v2, with its own scripts (`review/Claude_review_*`). |

**Consequences.**
- Errors of the kind AI systems make (misquoted constants, inputs used outside their range of validity, overlooked hypotheses) are the main risk. Several such errors were found and fixed during the project; all are recorded in `LOG.md`, in manuscript Appendix C, and in the review responses.
- The withdrawn k = 67 claim is an example: it was made before its key input had been audited.
- The full conversation that produced this work is in [`proof/conversation/`](proof/conversation/) (Chinese original, English translation). It contains statements that were later corrected; the manuscript is authoritative.

## Inputs and their status

| Input | Source | Status | Used by |
|---|---|---|---|
| RH verified to height 3·10¹² | Platt–Trudgian 2021 | refereed | both |
| N(T) bound | Bellotti–Wong 2025 | refereed | both |
| zero-density (KLN-type) 17.418 / 2.231 | Johnston–Yang 2023 | refereed | both (negligible) |
| log-free zero density, Table 2 | Bellotti, *J. Number Theory* 2025 | refereed; checked against arXiv v2 only, **not yet against the printed table** | both |
| zero-free region, classical **4.896** | Bellotti–Trudgian–Yang, arXiv:2603.21490 | **preprint**; audited here | Theorem 1 |
| zero-free region, classical 5.558691 | Mossinghoff–Trudgian–Yang 2024 | refereed | Theorem 2 |
| zero-free region, Littlewood 21.233 | Yang, *JMAA* 2024 | refereed | both |
| zero-free region, Vinogradov–Korobov 54.004 | Bellotti, *JMAA* 2024 | refereed | both |
| truncated explicit formula | Cully-Hugill–Johnston II 2025 | refereed | both |
| ψ − θ bounds | Broadbent–Kadiri–Lumley–Ng–Wilk 2021 | refereed | both |
| prime-interval pairs (Δ, x₀) | Cully-Hugill–Lee 2022 + corrigendum 2024 | refereed; checked against arXiv v3 | both |
| ζ(1/2+it) bound (an upstream input) | Hiary–Patel–Yang 2024, plus our Arb check | refereed + verified | both |

The full statements of these inputs are in manuscript §3.1. [`SOURCES.md`](SOURCES.md) has links to all papers. The papers themselves are not redistributed here.

## How to review

| If you want to … | Start with |
|---|---|
| read the argument | [`proof/manuscript.md`](proof/manuscript.md) (English, v4) |
| check specific items | [`proof/REVIEW_CHECKLIST.md`](proof/REVIEW_CHECKLIST.md), ordered by how much the conclusion depends on them |
| see the reviews so far | [`review/`](review/) (Chinese) and our [response](review/response_to_reviews_2026-11-06.md) |
| check the zero-free-region audit | [`proof/zfr_audit/README.md`](proof/zfr_audit/README.md) |

The highest-value checks are:
1. BTY Theorem 1 (4.896), which only Theorem 1 needs;
2. the printed JNT version of Bellotti's Table 2;
3. Lemma 4 (smooth explicit formula via ψ₁);
4. Propositions H and S and Lemma T;
5. a second, independent rigorous implementation of δ_S.

**Re-run the numerics** with Python 3 and python-flint 0.9.0. It takes about 15 minutes; compare the output with `proof/certificates/verify_all_output.txt`.

```bash
cd proof/code
pip install -r requirements.txt
python verify_all.py
```

**Build the Lean part** with Lean 4.36.0-rc2 and Mathlib. `Audit.lean` should list only the axioms `propext`, `Classical.choice` and `Quot.sound`.

```bash
cd proof/LegendreK67
lake exe cache get
lake build
lake env lean LegendreK67/Audit.lean
```

Please report problems as GitHub issues, quoting a checklist ID if possible (e.g. `A5: ISSUE — …`).

## Repository layout

| Path | Contents |
|---|---|
| `proof/` | **The review package. This is the authoritative version.** It contains the manuscript, checklist, certificates, verification code, the Lean project, the audit and the conversation. |
| `review/` | External AI reviews and our responses |
| `SOURCES.md` | Literature with links |
| `ROADMAP.md`, `LOG.md` | Research roadmap and lab log (Chinese), including every bug found |
| `code/`, `docs/`, `results/` | Exploratory working files from earlier stages. Many of them use superseded constants or the withdrawn k = 67 setting. They are kept for the record and are **not** part of the claims. |

The folder and Lean package are still named `legendre_k67` / `LegendreK67` for historical reasons: the project started with k = 67 as its target.

## History

| Version | Change |
|---|---|
| v1 | k ≥ 67 claimed, using inputs as quoted in Lee (2026). |
| v2 | Inputs checked against the original sources; four quoted inputs replaced. |
| v3 | Revised after two AI reviews (Codex, Claude). |
| v4 (2026-11-06) | The audit found an arithmetic error in the thesis proof of 19.62, on which k = 67 depended. **k = 67 withdrawn**; interim results k ≥ 70 and k ≥ 74. Lean generalised to a parameter k₀. |

## Key references

The full list is in the manuscript and in [`SOURCES.md`](SOURCES.md).

- E. S. Lee, *Minimal zero-free regions for results on primes between consecutive perfect kth powers*, Acta Arith. 225 (2026) 149–162.
- M. Cully-Hugill, D. R. Johnston, *On the error term in the explicit formula of Riemann–von Mangoldt* II, Funct. Approx. Comment. Math. 73 (2025).
- M. Cully-Hugill, E. S. Lee, *Explicit interval estimates for prime numbers*, Math. Comp. 91 (2022); Corrigendum 93 (2024).
- C. Bellotti, *An explicit log-free zero density estimate for the Riemann zeta-function*, J. Number Theory 269 (2025).
- C. Bellotti, T. Trudgian, A. Yang, *Zero-free regions inspired by work of Heath-Brown*, arXiv:2603.21490.
- M. J. Mossinghoff, T. S. Trudgian, A. Yang, *Explicit zero-free regions for the Riemann zeta-function*, Res. Number Theory 10 (2024).
- A. Yang, *Explicit bounds on ζ(s) in the critical strip and a zero-free region*, J. Math. Anal. Appl. 534 (2024).
- D. R. Johnston, A. Yang, *Some explicit estimates for the error term in the prime number theorem*, J. Math. Anal. Appl. 527 (2023).

## License

The code, the Lean files and the documents are released under the Apache License 2.0 (`LICENSE`). Third-party papers are not included.

---

## 中文摘要

**结论（阶段性，未经同行评审）**
- 对所有 k ≥ 70、n ≥ 1，区间 (n^k, (n+1)^k) 中都有素数。唯一未经评审的文献输入是 Bellotti–Trudgian–Yang 的经典零点自由区域常数 4.896（arXiv 预印本），本项目已独立核实其证明。
- 只用经过同行评审的文献输入，得到 k ≥ 74。
- 此前已发表的最好结果是 k ≥ 86（Lee 2026）。
- 早先声称的 k ≥ 67 **已撤回**：它依赖的 19.62 的证明中，我们发现了一处算术错误。

**核心贡献**
- 在 Lee / Cully-Hugill–Johnston 的框架内加入四项改进：拼接密度估计、光滑化显式公式、Bellotti 表的低高度行、自证的尾部引理。
- 对全部文献输入逐一核对原文。
- 独立核验了两个零点自由区域常数。
- 全部数值用 Arb 严格计算并给出证书；Lean 形式化了记账部分。

**AI 参与程度**
- 本项目几乎完全由 AI 自主完成：
  - 选题阶段，Codex（OpenAI）帮助项目发起人筛选适合用 AI 攻克的问题，挑出了勒让德型问题；
  - Claude（Anthropic，Opus 5.5）完成了文献、推导、代码、证书、Lean 和文稿；
  - 评审由 Codex 和另一个 Claude 实例完成。
- 项目发起人负责提出问题、确定方向和质量要求，并决定结论的表述，**没有独立核验数学内容**。

**请批评指正**
- 请从 `proof/manuscript.md` 和 `proof/REVIEW_CHECKLIST.md` 开始审查，问题请在 Issues 中提出。
- 文中对他人工作（博士论文中的 19.62、BTY 的若干笔误）的判断是我们的理解，欢迎指正。
