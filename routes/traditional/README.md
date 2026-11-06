# Traditional explicit-estimate route / 传统显式估计路线

[Repository overview / 仓库总览](../../README.md)

**AI authors: Claude and Codex. Route lead: Claude.** Codex leads the separate
QRH(7/8) route and contributed topic selection and review here. The project
owner directs the research; no complete human expert verification is recorded.

## Result and evidence

This route does not assume QRH(7/8). Its current public review manuscript gives
computer-assisted arguments for all positive integers n:

| Variant | Exponents k | Literature inputs |
|---|---|---|
| Main explicit-estimate variant | Every integer k >= 70 | The listed inputs, including BTY's preprint zero-free-region constant 4.896 |
| Refereed-input variant | Every integer k >= 74 | The listed refereed inputs, with 5.558691 replacing 4.896 |

The new arguments remain subject to review in both variants. The earlier
k >= 67 claim was withdrawn; the audit and earlier certificates are retained.
Lean checks assembly under explicit analytic and certificate hypotheses,
not the full analytic proof.

- [Current manuscript](proof/manuscript.md) and [review package](proof/README.md)
- [Review checklist](proof/REVIEW_CHECKLIST.md), [input sources](SOURCES.md),
  [zero-free-region audits](proof/zfr_audit/README.md)
- [Current certificates](proof/certificates/) and [numerical replay record](proof/certificates/verify_all_output.txt)
- [Lean project and scope](proof/lean/README.md)
- [Historical AI reviews](review/), [research log](LOG.md), and [roadmap](ROADMAP.md)

From this route directory:

```sh
python -m pip install -r proof/code/requirements.txt
python proof/code/verify_all.py
```

For Lean, enter `proof/lean/` and follow its README. The internal package name
`LegendreK67` is retained for compatibility; the repository is organized by
research route, not by the exponent appearing in a theorem or certificate.

`code/`, `docs/`, and `results/` hold earlier exploratory work. Some historical
review scripts expect older certificate locations or locally downloaded
third-party sources that are not distributed. Their original reports and
commands describe those historical versions; use `proof/code/verify_all.py`
for the current main numerical claims. The source-specific audit readmes state
additional inputs where needed.

The route retains the repository's [Apache-2.0 license](../../LICENSE).
Dependencies and cited works keep their own licenses.

## 中文入口

**AI 作者：Claude、Codex；本路线负责人：Claude。** Codex 负责另一条 QRH(7/8) 路线，
并对本路线贡献选题与审阅。项目发起人负责方向和质量要求，尚无完整人类专家核验的记录。

本路线不假定 QRH(7/8)。当前公开审查稿在列明输入下给出全体 n ≥ 1 的结果：
采用含 BTY 预印本常数 4.896 的输入组时，覆盖全部整数 k ≥ 70；只采用经评审文献输入的
版本覆盖全部整数 k ≥ 74。两种版本的本项目新增论证均仍待审阅。早期 k ≥ 67 结论已撤回，
相关历史与审计材料保留。

正式成果从 [proof/ 审查包](proof/README.md)进入；数学正文为英文，
复算命令见上文。Lean 的实际项目目录为 `proof/lean/`，内部包名仍为 `LegendreK67`，
只表示历史兼容，不表示恢复了 k = 67 结论。Lean 的范围是显式解析与证书假设下的逻辑拼接。

较早的 `code/`、`docs/`、`results/` 及历史审阅按原版本保留，不能当作当前主结论。
某些历史复算依赖未随仓库分发的第三方资料或旧证书位置；当前数值复核入口是
`proof/code/verify_all.py`。本路线沿用根目录 Apache-2.0 许可。
