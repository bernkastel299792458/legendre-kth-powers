# proof/ — 审查包：相邻 k 次方之间的素数（阶段性成果，v4）

**状态：待审查，尚未经过同行评审。** 这是一个计算机辅助的论证，并且以若干文献输入为前提。

**AI 参与：**
- 本项目几乎完全由 AI 自主完成。
  - 选题由 ChatGPT（OpenAI）帮助筛出；
  - Claude（Anthropic，Opus 5.5）完成了全部推导、代码、证书、Lean 和文稿；
  - 评审由 GPT 与另一个 Claude 实例完成。
- 项目发起人负责提出问题、确定方向和质量要求，**没有独立核验数学内容**。
- 详见手稿开头的"Authorship and AI involvement"。英文总览见仓库根目录 `README.md`。

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
| v3 | 吸收 GPT 与 Claude 两份 AI 评审（`../review/`） |
| v4 | 核验零点自由区域常数；撤回 k = 67；以 k = 70 / 74 为阶段性成果；Lean 改为参数 k₀ |

## 目录

| 路径 | 内容 |
|---|---|
| `manuscript.md` | **主手稿（英文，v4）** |
| `REVIEW_CHECKLIST.md` | 审查清单 |
| `input_verification/` | 文献核对报告（第三方原文没有随仓库上传，见 `SOURCES.md`） |
| `zfr_audit/` | 对 4.896 与 19.62 的独立核验（报告、复算脚本、部分 Lean） |
| `certificates/` | k = 70、74 的证书，`verify_all_output.txt`，`sanity_small_k.txt`，`sensitivity_output.txt`（输入敏感性）；`withdrawn_k67/`、`superseded_*` 是旧证书 |
| `code/` | 严格验证代码；运行 `verify_all.py` 一键复核；`make_chain.py` 生成证书链；`scan_min_k.py` 扫描最小 k；`sensitivity.py` 做输入敏感性分析 |
| `LegendreK67/` | Lean 4 + Mathlib 形式化（只覆盖记账部分） |
| `conversation/` | 研究对话记录（中文原文与英文翻译） |

## 如何复核

**数值部分**（全程纯 Arb，约 15 分钟）：

```bash
cd code
pip install -r requirements.txt
python verify_all.py
```

**Lean 部分：**

```bash
cd LegendreK67
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
