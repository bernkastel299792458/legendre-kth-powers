# 相邻 k 次幂之间的素数

[English](README.md) | **简体中文**

**AI 作者：Claude 与 Codex。** Claude 负责传统路线，Codex 负责 QRH(7/8) 路线。
[作者与贡献](AUTHORS.md) · [协作协议](RESEARCH_PROTOCOL.md)

本仓库研究：对哪些整数 k，**每个整数 n ≥ 1** 的开区间
`(n^k, (n+1)^k)` 中都存在素数。项目包含两条研究路线，分别采用不同的数学前提，
各有自己的审查包和验证记录。

**状态（2026-11-06）：** 公开审查稿，研究工作主要由 AI 系统完成。
两条路线均尚无完整人类专家审阅的记录，也均未完成全部解析论证的端到端 Lean 形式化。

## 成果总览

下表每项结论均覆盖**所有正整数 n**，并以对应文献输入和本项目稿件中的新论证为基础。

| 研究路线 | 当前报告的成果 | 主要前提 | 审查入口 |
|---|---|---|---|
| **A. 传统显式估计路线** | 所有整数 **k ≥ 70** | 列明的显式估计，包括 Bellotti–Trudgian–Yang 预印本的零点自由区域常数 **4.896**；不假定 QRH | [传统路线论文，英文](routes/traditional/proof/manuscript.md) |
| **A. 传统路线，仅用经评审文献输入的版本** | 所有整数 **k ≥ 74** | 列明的经同行评审文献输入，以 **5.558691** 替代 4.896；不假定 QRH | [传统路线审查包](routes/traditional/proof/README.md) |
| **B. 假定 QRH(7/8) 成立的路线** | 固定指数 **k = 6** | **H1：** 所有非平凡 ζ 零点的实部不超过 7/8；**H2：** CS **arXiv:2507.15184v2** 推论 1 及指定表格行，另加列明的辅助输入 | [QRH 路线审查包](routes/qrh/README.md) · [中文论文 PDF](routes/qrh/paper/main.pdf) |

“仅用经评审文献输入”描述的是所用文献的状态，不表示本项目的新证明已经通过同行评审。
两条路线的数学前提不同，比较指数时必须同时说明这些前提。

## 路线 A：传统显式估计

### 结论与方法

[v4 论文](routes/traditional/proof/manuscript.md)给出计算机辅助论证，覆盖所有整数 **k ≥ 70**；
若将文献输入限制为经同行评审的结果，则覆盖所有整数 **k ≥ 74**。

这条路线结合显式零点自由区域、混合零点密度估计、平滑显式公式、有限区间证书和解析无限尾部。
它**不假定 QRH(7/8)**。

k ≥ 70 版本使用预印本常数 4.896。项目的
[AI 核查报告](routes/traditional/proof/zfr_audit/bty_4.896/REPORT.md)认为，按报告列出的修正处理后，其证明可以成立；
该核查不是人类同行评审。k ≥ 74 版本使用经评审的常数 5.558691。
两者还使用 21.233、54.004 及论文列明的其他输入。

### 证据与验证范围

数值区间由 Arb 证书覆盖。Lean 在**假定列明的解析估计和证书结论成立**时，
检查各区间的逻辑拼接；它没有证明这些解析估计或 Arb 计算本身。
详见[审查清单](routes/traditional/proof/REVIEW_CHECKLIST.md)、
[数值重放记录](routes/traditional/proof/certificates/verify_all_output.txt)和
[Lean 覆盖范围](routes/traditional/proof/README.md#lean-证明了什么)。

文献核对和待审事项分别记录在
[SOURCES.md](routes/traditional/SOURCES.md)、[输入核查](routes/traditional/proof/input_verification/)和
[零点自由区域核查](routes/traditional/proof/zfr_audit/README.md)中。
其中 Bellotti 的表格目前核对的是 arXiv v2，与期刊印刷版表格逐项比对仍是待审事项。

**早先的 k ≥ 67 结论已经撤回。** 项目核查在所需常数 19.62 的博士论文证明中发现了算术问题。
这一判断是本项目对原文的理解，尚不是经原作者确认的勘误。
参见[核查报告](routes/traditional/proof/zfr_audit/thesis_19.62/REPORT.md)和
[撤回结论的历史证书](routes/traditional/proof/certificates/withdrawn_k67/README.md)。
Lean 项目保留的历史名称 `LegendreK67` 不代表当前仍声称证明了 k = 67。

## 路线 B：假定 QRH(7/8) 成立

### 结论与显式前提

本路线选择接受 QRH(7/8) 作为研究起点，依据是 OpenAI 已在
[官方 openai/math 仓库](https://github.com/openai/math)公开了署期 2026 年 9 月 30 日的
[7/8 无零半平面证明论文](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/README.md)及配套 Lean 材料。
我们将其中关于 ζ 非平凡零点实部不超过 7/8 的结果作为明确的上游输入，
集中研究它对相邻幂之间素数问题的后续推论。

OpenAI 的[Family 003 专项说明](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/docs/003.md)明确列出了该 7/8 结果的形式化范围。
我们尚未独立重建其完整证明依赖或运行上游 Comparator，因此在定理前提中继续显式保留 H1。
上游 QRH 的形式化与本项目尚未完成的素数区间论证端到端形式化是两件不同的事。

此外，明确依赖 Chourasiya–Simonič 的 **v2** 密度结果，并将其作为预印本输入处理：
推论 1、表 1 中编号 **16–27** 的行（即前 12 行），以及这些行规定的适用域。
所引经典辅助定理另列于[论文](routes/qrh/paper/manuscript.md)。

在这些前提下，书面论证给出：对每个整数 n ≥ 1，存在素数 p，使

```text
n^6 < p < n^6 + 6n^5 < (n+1)^6。
```

结论同时依赖 **H1 和 H2**，不能只写成“假定 QRH 即得”。
本项目尚未得到 k = 4 或 k = 3 的全范围结论；两者分别仍是阶段目标和长期研究目标。

### 证据与验证范围

审查包结合了 1259 个小范围素数见证、CHL 区间表、**94** 个中段单元、
**60** 个后续单元及解析无限尾部。
加密后的中段上界不超过 `0.939735996783828324763044`。
固定其他输入、指数和适用域后，CS 三列系数统一增大 **6%**，书面证明的全链仍能通过。
这项敏感性检验不认证 CS 定理本身。

**46 个 Lean 模块**已通过编译，其中包括全部 1259 个素数见证的实际 Lucas/Pratt 证明、
精确区间归约、有理证书比较、部分解析引理及标量尾界。
但当前最终装配定理的类型仍然是

```text
CHLRows -> AnalyticSegmentInputs -> SixthPowerConclusion
```

`AnalyticSegmentInputs` 中的三个局部解析结论，尚未在 Lean 中由 H1/H2 和列明文献输入推出。
实际 ζ 显式公式与密度估计的论证、完整单元超越表达式的上界，仍需在 Lean 中连接起来。
详见[形式化状态](routes/qrh/FORMALIZATION_STATUS.md)和
[完整定理类型及公理审计](routes/qrh/audit/kernel_axioms.txt)。

发布包在提交 `58521b6` 上通过了
[Linux 数值与 Lean 自动复核](https://github.com/bernkastel299792458/legendre-kth-powers/actions/runs/42153017737)。
这验证的是明确列出的计算和部分形式化范围，不是该条件定理的端到端 Lean 证明。

## 阅读、复现与审查

| 目的 | 传统路线 | QRH 路线 |
|---|---|---|
| 阅读论证 | [英文论文](routes/traditional/proof/manuscript.md) | [中文论文](routes/qrh/paper/manuscript.md) · [PDF](routes/qrh/paper/main.pdf) |
| 检查输入 | [论文第 3 节](routes/traditional/proof/manuscript.md) · [文献来源](routes/traditional/SOURCES.md) | [论文第 1 节](routes/qrh/paper/manuscript.md) · [BibTeX](routes/qrh/paper/references.bib) |
| 复现计算 | [审查包复算说明](routes/traditional/proof/README.md#如何复核) | [复现说明](routes/qrh/REPRODUCING.md) |
| 理解 Lean 范围 | [逻辑拼接的范围](routes/traditional/proof/README.md#lean-证明了什么) | [已完成部分与剩余义务](routes/qrh/FORMALIZATION_STATUS.md) |
| 审查证据 | [清单](routes/traditional/proof/REVIEW_CHECKLIST.md) · [AI 审阅与答复](routes/traditional/review/) | [范围审阅](routes/qrh/audit/PUBLICATION_SCOPE_REVIEW.md) · [历史审阅](routes/qrh/audit/source_reviews/README.md) |

**传统路线数值重放**，从仓库根目录运行：

```sh
python -m pip install -r routes/traditional/proof/code/requirements.txt
python routes/traditional/proof/code/verify_all.py
```

**QRH 路线数值重放**，使用 **Python 3.12.10**，从仓库根目录运行。
冻结的尾部检查器会比较包含 Python 补丁版本在内的元数据。

```sh
python -m pip install -r routes/qrh/code/requirements.txt
python routes/qrh/code/release_manifest.py --check
python -X utf8 routes/qrh/code/verify_k6.py --dry-run
python -X utf8 routes/qrh/code/generate_lean_certificates.py --check
```

两个审查包均使用 python-flint 0.9.0。各自的复现说明包含独立的 Lean 构建步骤及进一步审查命令。
CI 通过、没有 `sorry` 或只依赖标准公理，都必须结合完整定理前提理解。
发现问题可通过 [GitHub Issues](https://github.com/bernkastel299792458/legendre-kth-powers/issues)反馈，
请注明路线、文件或定理以及版本。

## 人类指导与 AI 贡献

| 角色 | 已记录的贡献 |
|---|---|
| **项目发起人** | 确定问题、研究方向、质量要求、核查任务和发布决定；没有独立核验数学内容。 |
| **Codex：选题** | 协助将勒让德型问题确定为研究目标。 |
| **Claude：传统路线** | 完成文献整理、推导、代码、证书、Lean 逻辑拼接和论文；不同会话承担常数核查及对话翻译。 |
| **Codex 与另一个 Claude 实例：传统路线审阅** | 提供 `routes/traditional/review/` 中的 AI 审阅及相应核查。 |
| **Codex：QRH 路线** | 完成条件性论证、加密证书、Lean 模块、论文和复现包，并由不同代理上下文交叉检查。 |
| **Claude：QRH 路线早期审阅** | 审阅较早的 76 单元版本，其建议推动了 CS v2 前提的明确化和数值余量的增强；该报告不认证后续新增的 Lean 实现。 |

AI 之间意见一致不能替代数学证明或人类专家审查。
传统路线论文附有具体贡献声明及[研究对话记录](routes/traditional/proof/conversation/)；
QRH 路线另有 [AI 使用声明](routes/qrh/AI_USE.md)。
QRH 论文的人类作者署名、单位和邮箱暂未填写。

## 仓库目录与许可证

研究材料按**路线**归档，不按指数 k 分设研究目录。证明实现中的 `LegendreK6`、
历史命名空间 `LegendreK67` 等名称保留，以维持已审计数学源码的字节一致性。
传统路线的 Lean 项目外层目录现为 `routes/traditional/proof/lean/`。
旧路径对应关系见[迁移说明](MIGRATION.md)。

```text
routes/
  traditional/   # Claude：显式估计、论文、代码、证书、Lean
  qrh/           # Codex：QRH(7/8)、论文、代码、证书、Lean
AUTHORS.md
RESEARCH_PROTOCOL.md
AGENTS.md
```


| 位置 | 内容 | 许可范围 |
|---|---|---|
| `routes/traditional/proof/` | 当前传统路线审查包：论文、证书、代码、Lean、输入核查和研究对话 | [Apache-2.0](LICENSE) |
| `routes/traditional/review/`、`routes/traditional/SOURCES.md`、`routes/traditional/ROADMAP.md`、`routes/traditional/LOG.md` | 传统路线审阅、文献、研究计划和历史日志 | [Apache-2.0](LICENSE) |
| `routes/traditional/code/`、`routes/traditional/docs/`、`routes/traditional/results/` | 传统路线早期工作文件，包括已替换的常数和已撤回的设定；当前结论以 `routes/traditional/proof/` 为准 | [Apache-2.0](LICENSE) |
| `routes/qrh/` | QRH 路线论文、证书、代码、Lean、范围声明、审计记录和发布哈希 | 原创代码 **0BSD**；原创论文、文档及数据 **CC0-1.0**。见[包内许可](routes/qrh/LICENSE)。 |

根目录 [LICENSE](LICENSE) 给出默认 Apache-2.0 条款，条件性研究包单独声明自己的许可范围。
第三方作品和依赖保留原有许可证；所引论文通过链接提供，不随本仓库重新分发。
