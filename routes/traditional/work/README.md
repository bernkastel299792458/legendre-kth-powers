# work/ — the v5 research workspace (traditional route)

[Route entry](../README.md) · [v5 status log](v5/STATUS.md) · [v5 certificates](v5/README.md)

**Status (2026-11-07).** The v5 certificate chains for **k = 37** and k = 41 pass the separate pure-Arb re-check `v5/check5.py` (CHAIN VERIFIED). The checker was written by the same author as the generator, so it is not an independent review. A chain for k = 36 fails at five narrow points of the seam (largest δ 1.046; [v5/STATUS.md](v5/STATUS.md)). The literature inputs are refereed results only. The chains also use new lemmas of this project that have had AI review only (listed below). Nothing here has had human peer review, and there is **no consolidated v5 manuscript yet**: the argument is the v4 manuscript's framework (`../proof/manuscript.md`) with the zero-sum majorant replaced, and the new lemmas are written up in the reports of each workstream.

**Why v5 exists.** The v4 results (k ≥ 70 / k ≥ 74) use the printed Table 2 of C. Bellotti's log-free zero-density estimate (J. Number Theory 269 (2025)). Our audit ([phase0_bellotti/REPORT.md](phase0_bellotti/REPORT.md) §1), confirmed by a separate AI review ([review_phase0/](review_phase0/)), found a counting gap in §4 of that paper. With her own parameters, the corrected constants C are about 2.0–2.2 times the printed ones. v4 tolerates only ×1.1 (k ≥ 70) and ×1.05 (k ≥ 74), so **the v4 results are not supported as stated**. v5 repairs the counting, re-derives the table, and improves it.

## Contents

| Directory | What it holds | Report |
|---|---|---|
| [CONTEXT.md](CONTEXT.md) | Shared brief for the v5 push (method, levers, file map), as written at the start | — |
| [phase0_bellotti/](phase0_bellotti/) | Audit of Bellotti §4. Arb implementation and corrected table. Re-optimised rows, including low-height (`rows_low_v3.csv`) and mid-height (`rows_mid_v4.csv`) rows. `verify_rows.py` re-checks every row | [REPORT.md](phase0_bellotti/REPORT.md) |
| [phase1_littlewood/](phase1_littlewood/) | Height-dependent Littlewood zero-free region, v1 and v2 (thesis method, own proof). Theorem C: height-dependent classical region by the BTY method (own proof, refereed inputs) | [REPORT.md](phase1_littlewood/REPORT.md) |
| [phase1_cs/](phase1_cs/) | Audit of Chourasiya–Simonič Cor. 1 (used only in exploratory tiers). Low-σ KLN-type constants (`kln_rows_low_sigma.csv`). Theorem R (fourth-moment constant b₄) | [REPORT.md](phase1_cs/REPORT.md) |
| [phase2_lemmas/](phase2_lemmas/) | New Lemmas A, B, B-W, C, D, which shrink Bellotti's constant C | [REPORT.md](phase2_lemmas/REPORT.md) |
| [audit_rza/](audit_rza/) | Audit of Ramaré–Zuniga Alterman inputs used by Lemma A | [REPORT.md](audit_rza/REPORT.md) |
| `review_*` | Separate AI reviews of the workstreams (other Claude instances), with their re-runs | each folder |
| [ref/](ref/) | Float models and early experiments (`belmodel.py`, `bv.py`, `lp.py`, …) | — |
| [v5/](v5/) | Zero-sum majorant Φ (`phi5.py`), rigorous δ bounds (`rig5.py`), chain generator and checker, inputs, certificates, scan logs | [STATUS.md](v5/STATUS.md), [README.md](v5/README.md) |

## Inputs of the k = 37 chain and their provenance

`v5/inputs/` holds byte copies of the workstream outputs; the certificate sidecar `v5/certs/<tag>.json` records the SHA256 of each.

| v5 input | Copy of | Produced and checked by |
|---|---|---|
| `bel_faithful_v2.csv` | `phase0_bellotti/rows_corrected_faithful.csv` | phase0 `verify_rows.py` |
| `bel_reopt_v1.csv`, `bel_reopt_v2.csv` | `phase0_bellotti/rows_reopt.csv`, `rows_reopt_v2.csv` | same |
| `bel_reopt_lam1_v1.csv` | `phase0_bellotti/rows_reopt_lam1.csv` (one number written as `1.01505E+6` instead of `1015050`; otherwise identical) | same |
| `bel_high_v1.csv`, `bel_high_v2.csv` | `phase0_bellotti/rows_high.csv`, `rows_high_v2.csv` | same |
| `bel_low_v3c.csv` | `phase0_bellotti/rows_low_v3.csv` | same |
| `bel_mid_v4a.csv` | the 900 rows of `phase0_bellotti/rows_mid_v4.csv` on log T ∈ [110, 350], byte-identical lines (an earlier output of `v4.py`, before the rows on [350, 600] were finished) | same |
| `zfr_local_v2.csv` | `phase1_littlewood/zfr_local_v2.csv` | phase1 certification scripts |
| `zfr_classical_local_v1.csv` | `phase1_littlewood/zfr_classical_local.csv` (Theorem C) | `check_cl.py`, `cert_classical.py` |
| `kln_low_v1.csv` | `phase1_cs/kln_rows_low_sigma.csv` | phase1_cs scripts |

## Our own lemmas used by the k = 37 chain

All of them are written up in the reports above and were checked by separate AI reviews (other Claude instances). None has had a human referee.
- The repair of Bellotti's §4 counting and the λ-box argument (phase0 §1).
- Lemmas A, B, B-W, C, D (phase2).
- Theorem C, the local classical zero-free constants (phase1 §12), and the local Littlewood constants v1/v2 (phase1 §1–§11).
- The low-σ KLN-type constants: our own Arb computation of the published Kadiri–Lumley–Ng / Johnston–Yang method.

## Reproducing

Requirements: Python 3.12, `python-flint==0.9.0`, `numpy`. `scipy` is needed only to re-run the row optimisation.

```sh
cd routes/traditional/work/v5
python check5.py k37_T1_refereed_own_lemmas
```

`check5.py` re-computes every piece of the chain in Arb, from the CSV files and code modules whose SHA256 the sidecar records. It takes several hours on 4 cores. `prio.py` keeps the run at idle priority on a quarter of the logical CPUs; set `LEGENDRE_NPROC` to change the number of processes. The rows themselves are re-checked by `python verify_rows.py <file.csv>` in `phase0_bellotti/`.

## Not distributed

- Third-party papers, arXiv sources and downloaded literature: `phase2_lemmas/lit/`, `audit_rza/deps_lit/`, `audit_rza/src_dl/`, `audit_rza/lemma31/dl/` (and their copies under `review_b4/rerun/`), `phase1_cs/src/`, `phase1_cs/fourth_moment/src/`.
- Extracted text of papers, and Bellotti's own code, from `ref/` (see [CONTEXT.md](CONTEXT.md) for what they were). Links are in [SOURCES.md](../SOURCES.md).

Some historical scripts read these files and will not run without them. Absolute Windows paths in logs and sidecars refer to the development machine. `check5.py` resolves the recorded code modules next to itself.

This folder keeps the exact bytes of every file (`.gitattributes`: `* -text`), because the certificate sidecars record SHA256 values.

## 中文摘要

- **现状：** v5 的 k = 37、41 证书链都已通过另一套纯 Arb 复核（`v5/check5.py`）。k = 36 的证书链在交界区有 5 个窄峰失败，最大 δ 为 1.046。文献输入只用经评审的结果；另外用到本项目自己的新引理，这些引理只经过 AI 审阅，没有人工审稿。v5 还没有合并成一篇完整手稿。
- **v4 不再成立：** v4（k ≥ 70 / 74）用到了 Bellotti 印刷版的 Table 2，我们发现该文 §4 有计数缺口。修正后 C 约为印刷值的 2.0–2.2 倍，超出 v4 的容忍度（×1.1 / ×1.05）。
- **复核：** 进入 `v5/` 后运行 `python check5.py k37_T1_refereed_own_lemmas`，4 核需要数小时。
- **未随仓库分发：** 第三方论文、源码与 Bellotti 的代码，链接见 SOURCES.md。
