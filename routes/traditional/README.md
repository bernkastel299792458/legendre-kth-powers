# Traditional explicit-estimate route / 传统显式估计路线

[Repository overview / 仓库总览](../../README.md)

**AI authors: Claude and Codex. Route lead: Claude.** Codex leads the separate
QRH(7/8) route and contributed topic selection and review here. The project
owner directs the research; no complete human expert verification is recorded.

## Result and evidence

This route does not assume QRH(7/8). All rows concern every positive integer n.

| Version | Exponents k | Inputs | Status (2026-11-07) |
|---|---|---|---|
| **v5** | **Every integer k >= 37** | Refereed literature inputs only, plus new lemmas of this project (AI-reviewed only) | Arb certificate chain re-checked by `work/v5/check5.py`. No consolidated v5 manuscript yet. [work/](work/README.md) |
| v4, main variant | Every integer k >= 70 | Includes BTY's preprint constant 4.896 and **Bellotti's printed Table 2** | **Not supported**, see below |
| v4, refereed-input variant | Every integer k >= 74 | Refereed inputs, including **Bellotti's printed Table 2** | **Not supported**, see below |

**Why v4 is not supported.** Our audit found a counting gap in §4 of C. Bellotti's
log-free zero-density paper (J. Number Theory 269 (2025)); a separate AI review
confirmed it. This is our reading, not an author-confirmed correction. With
her own parameters the corrected constants are about 2.0–2.2 times the printed
Table 2, and v4 tolerates only ×1.1 (k >= 70) and ×1.05 (k >= 74). v5 repairs
the counting, recomputes the rows in Arb, and improves them with new lemmas;
see [work/phase0_bellotti/REPORT.md](work/phase0_bellotti/REPORT.md) and
[work/phase2_lemmas/REPORT.md](work/phase2_lemmas/REPORT.md).

**What v5 rests on.**
- The literature inputs are refereed: MTY, Yang, Bellotti (VK), Johnston–Yang, CHJ II, BKLNW, CHL, Platt–Trudgian, Bellotti–Wong, Hiary–Patel–Yang, Heath-Brown, Thorner–Zaman, Ford, Kadiri, Ramaré–Zuniga Alterman and others. They are listed in [SOURCES.md](SOURCES.md).
- Our own lemmas: the repaired §4 counting, Lemmas A, B, B-W, C, D, Theorem C (local classical zero-free constants by the BTY method), local Littlewood constants, and low-σ KLN constants. They have had separate AI reviews (other Claude instances), not human refereeing.
- The certificate checker was written by the same author as the generator.
- The v4 Lean assembly is not updated for v5.

The earlier k >= 67 claim was withdrawn; the audit and earlier certificates
are retained. The v4 Lean project checks the v4 assembly under explicit
analytic and certificate hypotheses, not the full analytic proof.

- [v5 workspace](work/README.md), [v5 certificates](work/v5/README.md), [v5 status log](work/v5/STATUS.md)
- [v4 manuscript](proof/manuscript.md) and [review package](proof/README.md) (historical; see above)
- [Review checklist](proof/REVIEW_CHECKLIST.md), [input sources](SOURCES.md),
  [zero-free-region audits](proof/zfr_audit/README.md)
- [Current certificates](proof/certificates/) and [numerical replay record](proof/certificates/verify_all_output.txt)
- [Lean project and scope](proof/lean/README.md)
- [Historical AI reviews](review/), [research log](LOG.md), and [roadmap](ROADMAP.md)

From this route directory:

```sh
python -m pip install -r proof/code/requirements.txt
cd work/v5 && python check5.py k37_T1_refereed_own_lemmas   # v5, several hours on 4 cores
python proof/code/verify_all.py                             # v4 replay record
```

For Lean, enter `proof/lean/` and follow its README. The internal package name
`LegendreK67` is retained for compatibility; the repository is organized by
research route, not by the exponent appearing in a theorem or certificate.

`code/`, `docs/`, and `results/` hold earlier exploratory work. Some historical
review scripts expect older certificate locations or locally downloaded
third-party sources that are not distributed. Their original reports and
commands describe those historical versions; use `work/v5/check5.py` for the
current v5 certificates and `proof/code/verify_all.py` for the v4 replay. The source-specific audit readmes state
additional inputs where needed.

The route retains the repository's [Apache-2.0 license](../../LICENSE).
Dependencies and cited works keep their own licenses.

## 中文入口

**AI 作者：Claude、Codex；本路线负责人：Claude。** Codex 负责另一条 QRH(7/8) 路线，
并对本路线贡献选题与审阅。项目发起人负责方向和质量要求，尚无完整人类专家核验的记录。

本路线不假定 QRH(7/8)。以下结论都对全体 n ≥ 1 成立。

- **v5（2026-11-07）：对全部整数 k ≥ 37 成立。**
  - 文献输入只用经评审的结果，另加本项目自己的新引理。这些引理只经过 AI 审阅，没有人工审稿。
  - Arb 证书链已由 `work/v5/check5.py` 复核。复核程序与生成程序出自同一作者。
  - 还没有合并成完整的 v5 手稿，入口是 [work/](work/README.md)。
- **v4（k ≥ 70 / k ≥ 74）目前不成立。**
  - 原因：v4 用到了 Bellotti（JNT 2025）印刷版的 Table 2，我们发现该文 §4 有计数缺口，另一个 AI 审阅也确认了。这是我们的判断，未经原作者确认。
  - 按她自己的参数，修正后的常数约为印刷值的 2.0–2.2 倍，超出 v4 的容忍度（×1.1 / ×1.05）。
  - v5 修正了计数，用 Arb 重算了整张表，并用新引理加以改进。
- **其他：** 早期 k ≥ 67 结论已撤回，相关历史与审计材料保留。v4 的 Lean 装配没有随 v5 更新。

v4 的 [proof/ 审查包](proof/README.md) 作为历史版本保留；数学正文为英文，
复算命令见上文。Lean 的实际项目目录为 `proof/lean/`，内部包名仍为 `LegendreK67`，
只表示历史兼容，不表示恢复了 k = 67 结论。Lean 的范围是显式解析与证书假设下的逻辑拼接。

较早的 `code/`、`docs/`、`results/` 及历史审阅按原版本保留，不能当作当前主结论。
某些历史复算依赖未随仓库分发的第三方资料或旧证书位置。v5 证书的复核入口是
`work/v5/check5.py`，v4 的复算记录入口是 `proof/code/verify_all.py`。本路线沿用根目录 Apache-2.0 许可。
