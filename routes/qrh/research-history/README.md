# QRH 路线研究档案

整理日期：2026-11-06。**本目录随 k=6 审查包公开，保留原始研究记录及其当时状态。** 发布材料与核验范围见[发布记录](../audit/publication_2026-11-06.json)。

这里保存研究怎样从 k=8 的背景进入 k=4 探索、形成 k=6 结果、接受审阅并完成七输入下游 Lean 证明。保存原文不表示当前认可其中每个陈述，也不把别的会话的候选纳入当前 k=6 证明。**本次没有运行旧探索程序或重新验证旧数学结论。**

当前结论及精确前提应查阅 [七输入登记](../documentation/inputs.md)；研究经过详见 [按阶段回顾](chronological_review.md)。

## 从背景到当前结果

以下顺序表示研究问题和证明依赖的演进，不把同日并行会话强行排成精确钟表时间。原文件的修改时间只作为快照元数据，不能充当研究事件的发生时间。

| 阶段 | 动机与变化 | 原始记录或现有审计 | 本次定位 |
|---|---|---|---|
| k=8 背景 | 梳理 OpenAI QRH、后续显式估计与 Visser k=8 路线 | [背景报告](snapshots/legacy-20261106/GPT_OpenAI_QRH_status_2026-11-06.md) | 原创资料整理；未复制第三方论文，未在本次重审 k=8 证明 |
| k=4 初始路线 | 共用短区间框架测试多个 k，避免将逐个降低指数作为前置要求 | [路线图](snapshots/legacy-20261106/ROADMAP.md)、[首轮](snapshots/legacy-20261106/research/SESSION_2026-11-06.md)、[第二轮](snapshots/legacy-20261106/research/SESSION_2026-11-06_ROUND2.md) | 保留成功范围、失败点和反事实实验；没有全范围 k=4 结论 |
| k=6 梯形突破 | β 型权及加强密度包络未闭合过渡段，转用两个均匀密度卷积的梯形权 | [k5/6/7 比较](snapshots/legacy-20261106/research/K5_K6_K7_ASSESSMENT_2026-11-06.md)、[核探索](snapshots/legacy-20261106/research/K6_KERNEL_EXPLORATION.md)、[证明入口](snapshots/legacy-20261106/research/K6_PROOF.md) | 从候选扫描进入连续区间认证；历史口径须结合后续输入修订阅读 |
| 原 76 格与 Claude 审阅 | 最坏上界接近 1；审阅要求显式承认 CS v2 及修正文献版本 | [旧 76 格证书](snapshots/legacy-20261106/archive/k6_before_claude_revision_2026-11-06/results/smooth_k6_certificate.json)、[Claude 原审稿](../audit/source_reviews/Claude_K6_proof_review_2026-11-06.md) | AI 审阅，不是期刊接受；旧证书和失败粗格原样保留 |
| 94 格精化 | 细分关键单元、加密网格、保存常数放大余量 | [精化说明](snapshots/legacy-20261106/research/K6_REFINED_CERTIFICATE.md)、[94 格证书](snapshots/legacy-20261106/results/smooth_k6_certificate.json)、[逐项回应](../audit/source_reviews/Response_to_Claude_K6_2026-11-06.md) | 当时的数值/书面证明，不以此替代后续 Lean 连接 |
| M1 | 从真实 ζ 零点和四个命名输入导出无限尾段 | [M1 审阅](../audit/milestone1_review.md)、[实施日志](../audit/formalization_progress_2026-11-06.md) | 记录中的阶段结果；当时尚未全范围形式化 |
| M2 | 建立四点积分公式、实际零点上界与困难试点单元的内核连接 | [M2 审阅](../audit/milestone2_analytic_review.md)、[M2 工作日志](../audit/milestone2_worklog.md) | 试点区间 `[715/4,179]`，不是当时已完成全部中远段 |
| M3 | 补下中段、前向平移和新梯形远段，组装最终命题 | [M3 审阅](../audit/milestone3_final_review.md)、[最终检查点](../audit/milestone3_checkpoint.json) | 已记录七输入下完整下游形式化；上游七输入未重证 |
| 输入来源审查 | 将发表、版本、数值重放与本库形式化状态拆开 | [H4](../audit/input4_source_review_2026-11-06.md)、[H6](../audit/input6_source_review_2026-11-06.md)、[H7](../audit/input7_source_review_2026-11-06.md) | 保留 CHJII/CHL 版本缺口及 CHL 舍入见证问题；CS 独立审查由另一工作负责 |

## 并行 k=4 研究：只存档，未重新审阅

R3–R5 是其他研究会话继续推进 k=4 的材料，**不是本次七输入 k=6 形式化链的一部分**。原记录中“已认证”“独立复核”等词描述当时报告的检查范围，本次归档没有重跑或重新授予这些判断。

| 分支 | 档案入口 | 保留的边界 |
|---|---|---|
| R3 带限下端、梯形远段与结构分析 | [会话记录](snapshots/legacy-20261106/research/SESSION_2026-11-06_ROUND3.md)、[带限权](snapshots/legacy-20261106/research/K4_BANDLIMITED_ROUND3.md)、[单调远段](snapshots/legacy-20261106/research/K4_MONOTONE_ROUND3.md) | 历史报告的局部推进；不增加本次 k=6 输入 |
| R4 Selberg 下端推进 | [研究正文](snapshots/legacy-20261106/research/K4_SELBERG_ROUND4.md)、[会话记录](snapshots/legacy-20261106/research/SESSION_2026-11-06_ROUND4.md) | 原会话记录保留内部会话标识；索引不复述标识 |
| R5 高高度重新定基 | [PROOF](snapshots/legacy-20261106/theory_round5/PROOF.md)、[当时复核](snapshots/legacy-20261106/theory_round5/audit/REVIEW.md) | **输入扩大到 CS v2 Theorem 1、Corollary 5 及原表首行，并使用有限 RH；不能混同 k=6 的 H2（Corollary 1 指定十二行）** |
| R5 对数坐标上端候选 | [候选说明](snapshots/legacy-20261106/theory_round5/upper/LOG_KERNEL_CANDIDATE.md)、[冻结记录](snapshots/legacy-20261106/theory_round5/upper/FREEZE_MANIFEST.json) | 原文明确待独立解析审阅，不将 L≥360 候选改写为本次已证范围 |
| R5 下端谱边缘候选 | [候选说明](snapshots/legacy-20261106/theory_round5/lower/SELBERG_OVERSHOOT.md)、[数据](snapshots/legacy-20261106/theory_round5/lower/selberg_overshoot.json) | 参数与输入另列；不因有数值文件就并入正式覆盖 |
| R5 P150/D8 靶点 | [研究决策](snapshots/legacy-20261106/research/SESSION_2026-11-06_ROUND5.md)、[D8 归约](snapshots/legacy-20261106/research/K4_DENSITY_TARGET_ROUND5.md)、[反事实设计](snapshots/legacy-20261106/research/K4_FAR_REDESIGN_ROUND5.md) | D8 本身未证明，P150 是待证密度改进；充分条件与反事实预算不等于新增实际覆盖 |

旧材料存在状态表述差异：高高度定基正文及部分汇总报告 `L≥362`，另一些后续日志/决策仍沿用 `L≥372`。本次原样保存并在回顾中指出，未据此替其他会话宣布统一的最新 k=4 阈值。

## 快照范围与字节保证

快照为 [snapshots/legacy-20261106](snapshots/legacy-20261106/)，原相对路径保持不变，共 **177 件、3,782,882 字节**：

- `research/` 56 件；`code/` 27 件；`results/` 62 件（含原代码快照）。
- `theory_round5/` 13 件；旧 76 格归档 13 件。
- 根部 `README/ROADMAP/RUNBOOK/LOG` 及两份原创背景报告，共 6 件。

只选择项目原创的 Markdown、Python、JSON、CSV。第三方 PDF、依赖/源码库、`proof/`、`.lake`、`computation_branch/`、`algorithm_only/` 和编译产物未复制。已在仓库中的 Claude 审阅未重复复制，可沿上表访问。没有改变原工作区的文件或替换旧档案内容。

[snapshot_manifest.json](snapshot_manifest.json) 对每件文件登记原相对路径、字节数、SHA-256、源文件复制前后及归档结束时的复核、原换行情况和证据状态。[snapshots/.gitattributes](snapshots/.gitattributes) 使用 `* -text`，防止 Git 改写历史 CRLF/LF。新索引和清单使用 UTF-8/LF；历史文本不作换行、措辞或链接“修复”。

已检查明显凭证与外部作者/版权标记，未发现需要排除的密钥或第三方源代码。三份历史文件保留两个不同的内部会话 UUID，共四处出现；它们是研究分工记录中的会话标识，不是访问凭证或分享链接。项目发起人已授权公开本审查包，原记录继续按原字节保留。

快照清单及旧审计中的 `LOCAL_OWNER_REVIEW_ONLY_NO_PUSH` 等状态描述归档和核验当时的情况，不代表当前仍待发布授权；这些历史记录保持原样，后续状态见发布记录。

## 阅读及复核方式

先读本索引和 [阶段回顾](chronological_review.md)，再根据需要打开原始文件。快照不是一个依赖齐全的独立运行包，缺失材料、未随包提供的运行环境以及原本就失效的旧归档链接列在 [dependency_gaps.md](dependency_gaps.md) 和 [机器清单](dependency_gaps.json)。

只核对档案字节、不会运行旧研究程序的命令：

```text
python routes/qrh/research-history/snapshot_legacy.py --verify-only
```

生成快照的 [原创脚本](snapshot_legacy.py) 保留在本目录。它按固定白名单复制、检测源文件并发变化，并拒绝覆盖内容不同的已有快照；不运行 Git、旧探索程序或安装器。
