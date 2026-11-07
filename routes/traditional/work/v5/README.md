# v5 — certificate chains

[work/ overview](../README.md) · [status log](STATUS.md)

Each chain proves θ(x + h) − θ(x) > 0 with h = k·x^{1−1/k} for every L = log x above the Cully-Hugill–Lee lower range. That range ends at L₁ = k·log(kΔ(1−1/Δ)²) with Δ = 2.51949·10¹¹; the numeric facts at the junction are re-checked in Arb.
- **[L₁, L₂]:** Proposition S (smoothed explicit formula, weight y^M(1−y)^M).
- **[L₂, L₃ = 10¹⁰]:** Proposition H (sharp truncation).
- **[L₃, ∞):** Lemma T, with σ₁ = 0.93.

Zeros enter through the majorant Φ of `phi5.py`. On each height cell it takes the best of:
- N(t);
- Johnston–Yang (KLN-type) bounds;
- our low-σ KLN constants;
- the repaired and improved Bellotti rows, using the zero-free width η.

η is the running minimum of MTY 5.558691, the Littlewood 21.233, the VK 54.004, our local Littlewood bands and Theorem C.

A chain for k also gives every larger exponent: for x ≥ 1 and k′ > k, k′x^{1−1/k′} ≥ k·x^{1−1/k}.

## Certified chains (T1: refereed literature inputs and our own lemmas)

| Tag | k | L₁ | L₂ | S pieces, max δ | H pieces, max δ | `check5.py` |
|---|---|---|---|---|---|---|
| `k37_T1_refereed_own_lemmas` | **37** | 1131463/1024 (1104.944) | 38055/2 | 5518, 0.860166 | 49670, 0.999998 | CHAIN VERIFIED |
| `k41_T1_refereed_own_lemmas` | 41 | 629047/512 (1228.607) | 56093/4 | 3678, 0.824641 | 3628, 0.975 | CHAIN VERIFIED |

- The H range of k = 37 has a very thin margin (max δ 0.999998). Pieces with δ ≈ 0.99999 come from the v4 `pick_c`, which optimised a different bound. The margin is still rigorous; `check5.py` re-computes every piece.
- The generator is not part of the proof. `check5.py` re-computes every piece from the CSV rows and the hashed modules `phi5.py`, `rig5.py`, `cfg5.py`, `tail5.py`.

Files per tag:
- `certs/<tag>.json`: configuration and the SHA256 of every input;
- `certs/<tag>_S.csv` and `certs/<tag>_H.csv`: the pieces;
- `certs/<tag>.log`: the generator log.

The run logs are `cert37.txt` and `cert41.txt`.

```sh
cd routes/traditional/work/v5
python check5.py k37_T1_refereed_own_lemmas
```

## Failed attempt: k = 36

`certs/k36_T1_refereed_own_lemmas.json` and `.log` and `cert36.txt` record a run that failed. It added the mid-height rows `bel_mid_v4b.csv` and used H generator v2, which chooses c by minimising the rig5 bound itself.
- **H:** covers [24037/4, 10¹⁰] with 3873 pieces, max δ 0.491.
- **S:** fails at L = 1141.03, 1174.0, 1240.05, 1274.0 and 1324.0. The largest δ is 1.046, even at piece width 1/1024.
- No piece files were written.

The sampled scans had reported "min k = 36". They sample S every 25 in L and miss such narrow peaks, so a sampled minimum is an optimistic estimate, not a result.

## Historical chains (superseded, not current claims)

`k52_T4_bty_LW_CSB`, `k57_T2_ref_LW_CSB`, `k63_LW_CS_bty`, `k64_T3_bty_LW` and `k68_CS_unaudited` are intermediate steps of the v5 push. They use preprint inputs: BTY 4.896, Chourasiya–Simonič, or the unaudited CS option. They were made by earlier versions of `phi5.py`, `rig5.py` and `cfg5.py`. Their sidecar hashes no longer match the published modules, so `check5.py` stops with "input changed". They are kept as a record only.

## Scans and diagnostics

- `scan5.py` runs sampled minimal-k scans; the logs are `scan_*.txt`.
- `diag_seam.py` is the seam diagnostic.
- These are floating-point or sampled tools, not certificates.

## 中文摘要

- **已认证 k = 37（T1）：** 文献输入只用经评审的结果，另加本项目自己的引理。证书链 `k37_T1_refereed_own_lemmas` 已通过复核。k = 41 同样通过。
- **k = 36 失败：** S 段有 5 个窄峰，最大 δ = 1.046。抽样扫描漏掉了这些点。
- **推到更大的 k：** 对 x ≥ 1 与 k′ > k，有 k′x^{1−1/k′} ≥ k·x^{1−1/k}，所以 k 的结论推出所有更大的指数。
- **较早的 k52–k68 证书链：** 用到预印本输入，且由旧版代码生成，只作为历史记录保留。
