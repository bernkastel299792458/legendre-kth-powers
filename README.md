# Primes between consecutive k-th powers: k ≥ 70 (interim result)

A computer-assisted research project on Legendre-type statements: for **every** n ≥ 1, the interval (n^k, (n+1)^k) contains a prime.

> **Status: interim result, not peer-reviewed.** The argument depends on the explicitly listed inputs from the literature. We publish it for review by mathematicians and AI reviewers.

## Results (v4, 2026-11-06)

| | Statement | Inputs |
|---|---|---|
| **Theorem 1 (high confidence)** | For every k ≥ **70** and n ≥ 1, (n^k, (n+1)^k) contains a prime. | One non-refereed input: the classical zero-free-region constant 4.896 (Bellotti–Trudgian–Yang, arXiv:2603.21490). We audited its proof independently (`proof/zfr_audit/bty_4.896/`). It uses only published results. |
| **Theorem 2 (conservative)** | The same for every k ≥ **74**. | Refereed inputs only. |

Context:
- The best published result is k ≥ 86 (E. S. Lee, *Acta Arith.* 225 (2026)).
- Visser (arXiv:2610.20058) gives k = 8, but only conditionally on OpenAI's claimed 7/8 quasi-Riemann hypothesis, which is not peer-reviewed. If that claim holds, it supersedes the results here.
- **Withdrawn:** v1–v3 claimed k ≥ 67. That claim relied on the Littlewood constant 19.62 from a PhD thesis. Our audit found an arithmetic error in that proof (`proof/zfr_audit/thesis_19.62/REPORT.md`).

## Method in brief

The method follows Lee's explicit-formula / zero-density framework. The range of log x is split into four parts:

| log x | Method |
|---|---|
| up to 2135.07 (k = 70) or 2261.18 (k = 74) | Cully-Hugill–Lee interval estimates (Lemma 6) |
| up to 9521 (k = 70) or 7343 (k = 74) | smoothed explicit formula with weight y^M(1−y)^M (Prop. S) |
| up to 10^8 | sharp truncation with a hybrid zero-density bound: Johnston–Yang plus Bellotti's log-free table (Prop. H) |
| from 10^8 on | self-contained tail lemma using the published Vinogradov–Korobov region (Lemma T) |

All numerics use Arb ball arithmetic and are stored as re-checkable certificates. Lean 4 / Mathlib formalises the logical assembly (`main_k70`, `main_k74`). The analytic inputs and the certificates enter the Lean proof as hypotheses.

## Where to start

| Path | Contents |
|---|---|
| [`proof/`](proof/) | **Review package. This is the authoritative version.** |
| [`proof/manuscript.md`](proof/manuscript.md) | Manuscript v4 (English): statements, inputs (I1)–(I10) and their status, proofs |
| [`proof/REVIEW_CHECKLIST.md`](proof/REVIEW_CHECKLIST.md) | Checklist for reviewers |
| `proof/code/`, `proof/certificates/` | Verification code and certificates |
| `proof/LegendreK67/` | Lean 4 project |
| `proof/zfr_audit/` | Independent audit of the zero-free-region constants 4.896 and 19.62 |
| [`review/`](review/) | AI reviews (GPT, Claude) and our point-by-point response |
| [`SOURCES.md`](SOURCES.md) | The papers used, with links. The PDFs are not included. |
| `ROADMAP.md`, `LOG.md` | Research roadmap and log (Chinese) |
| `code/`, `docs/`, `results/` | Exploratory working files and earlier certificates, including the withdrawn k = 67. Kept for the record; superseded by `proof/`. |
| `proof/conversation/` | The research conversation with Claude (Chinese original and English translation) |

## How to verify

```bash
cd proof/code
pip install -r requirements.txt   # python-flint (Arb)
python verify_all.py              # pure Arb, about 15 minutes; compare with ../certificates/verify_all_output.txt
```

```bash
cd proof/LegendreK67
lake exe cache get
lake build
lake env lean LegendreK67/Audit.lean   # axioms: propext, Classical.choice, Quot.sound only
```

## Reporting problems

Please open an issue, quoting the checklist item ID (e.g. `A5: ISSUE — …`).

## Credits

This research was carried out with the assistance of AI systems: Claude did the research, the code and the drafting; GPT and Claude wrote independent reviews. Responsibility for checking the results lies with the reader. Nothing here is claimed as proved beyond what the listed inputs and the review status support.
