# proof/ — 审查包：相邻 k 次方之间的素数（阶段性成果，v4）

> **状态警示（2026-11-07）：本审查包（v4）的结论目前不成立，已由 v5 取代。**
> - **原因：** 两条定理都用到了 C. Bellotti 零点密度估计（JNT 2025）印刷版的 Table 2。我们的核验（`../work/phase0_bellotti/`）发现该文 §4 有计数缺口，另一个 AI 审阅也确认了；这是我们的判断，未经原作者确认。按她自己的参数，真实的 C 约为印刷值的 2.0–2.2 倍，而 k ≥ 70 只能容忍 ×1.1，k ≥ 74 只能容忍 ×1.05。
> - **现状：** v5 修正了计数并加入新引理，证书链对所有 k ≥ 37 通过复核（文献输入只用经评审的结果，新引理只经过 AI 审阅），见 [`../work/README.md`](../work/README.md)。本目录作为 v4 的历史版本保留，内容未改。

**状态：待审查，尚未经过同行评审。** 这是一个计算机辅助的论证，并且以若干文献输入为前提。

**作者：bernkastel299792458、Claude、Codex。** bernkastel299792458 为项目发起人；Claude 负责传统显式估计路线；Codex 负责仓库的 QRH(7/8) 路线，并在本稿中贡献选题与审阅。Claude 与 Codex 的署名记录 AI 系统贡献，不是人类作者身份或供应商背书。

**AI 参与：**
- 本项目几乎完全由 AI 自主完成。
  - 选题由 Codex（OpenAI）帮助筛出；
  - Claude（Anthropic，Opus 5.5）完成了全部推导、代码、证书、Lean 和文稿；
  - 评审由 Codex 与另一个 Claude 实例完成。
- 项目发起人负责提出问题、确定方向和质量要求，**没有独立核验数学内容**。
- 详见手稿开头的"Authorship and AI involvement"。路线入口见 [传统路线 README](../README.md)，双路线总览见 [仓库主页](../../../README.md)。

## 阶段性成果

| | 结论 | 依赖 |
|---|---|---|
| **高置信** | 对所有 k ≥ **70**、n ≥ 1，(n^k, (n+1)^k) 中都有素数 | 只有一个输入未经同行评审：经典零点自由区域常数 4.896（Bellotti–Trudgian–Yang, arXiv:2603.21490）。本项目已独立核实其证明（`zfr_audit/bty_4.896/`，修正了 15 处不致命的问题），且它只依赖已发表的结果 |
| **保守** | 对所有 k ≥ **74** 同样成立 | 只用已发表、经同行评审的输入 |

- 已发表的最好结果是 k ≥ 86（Lee，Acta Arith. 225 (2026)）。
- OpenAI 声称证明了 7/8 准黎曼猜想（未经同行评审）；Visser 以此为前提推出 k = 8（arXiv:2610.20058）。如果准 RH 成立，k = 70 / 74 就不再是纪录（手稿 §1.1）。
- **已撤回：** v1–v3 的 k = 67 依赖 Yang 博士论文中的 19.62。`zfr_audit/` 发现该证明有一处算术错误（引理 3.8），修复后 k = 67 闭合不了。旧证书移到了 `certificates/withdrawn_k67/`。

## 版本

| 版本 | 内容 |
|---|---|
| v1 | 引用 Lee 转述的输入 |
| v2 | 对照原始文献修正了 4 处问题 |
| v3 | 吸收 Codex 与 Claude 两份 AI 评审（`../review/`） |
| v4 | 核验零点自由区域常数；撤回 k = 67；以 k = 70 / 74 为阶段性成果；Lean 改为参数 k₀ |

## 目录

| 路径 | 内容 |
|---|---|
| `manuscript.md` | **主手稿（英文，v4）** |
| `REVIEW_CHECKLIST.md` | 审查清单 |
| `input_verification/` | 文献核对报告（第三方原文没有随仓库上传，见 [`../SOURCES.md`](../SOURCES.md)） |
| `zfr_audit/` | 对 4.896 与 19.62 的独立核验（报告、复算脚本、部分 Lean） |
| `certificates/` | k = 70、74 的证书，`verify_all_output.txt`，`sanity_small_k.txt`，`sensitivity_output.txt`（输入敏感性）；`withdrawn_k67/`、`superseded_*` 是旧证书 |
| `code/` | 严格验证代码；运行 `verify_all.py` 一键复核；`make_chain.py` 生成证书链；`scan_min_k.py` 扫描最小 k；`sensitivity.py` 做输入敏感性分析 |
| `lean/` | Lean 4 + Mathlib 形式化（只覆盖记账部分；内部包名保留 `LegendreK67`） |
| `conversation/` | 研究对话记录（中文原文与英文翻译） |

## 如何复核

以下两组命令均分别从本审查包 `routes/traditional/proof/` 出发。

**数值部分**（全程纯 Arb，约 15 分钟）：

```bash
cd code
pip install -r requirements.txt
python verify_all.py
```

**Lean 部分：**

```bash
cd lean
lake exe cache get
lake build
lake env lean LegendreK67/Audit.lean
```

## Lean 证明了什么

`main_k70` 和 `main_k74` 证明的是：**若** `Hypotheses k₀ L₁ L₂ L₃` 的各字段成立，**则**对所有 k ≥ k₀、n ≥ 1，区间 (n^k, (n+1)^k) 中有素数。

这些字段**没有**在 Lean 中证明：
- CHL 区间估计；
- 数值事实；
- 命题 S、命题 H 及其证书；
- Lemma T。

全部解析输入和 arb 计算同样不在 Lean 中。"无 `sorry`"只针对记账逻辑。
