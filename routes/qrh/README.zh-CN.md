# QRH(7/8) 路线：相邻六次幂之间的素数

[English](README.md) · [本次整理审核入口](REVIEW_THIS_RELEASE.md)

在下述七项明确输入成立时，对每个整数 **n ≥ 1**，存在素数

\[
n^6 < p < n^6+6n^5 < (n+1)^6.
\]

本项目已完成从七项输入到这一全范围结论的下游 Lean 形式化：241 个模块通过全新输出目录重建，最终定理不再含本项目局部区间结论或数值预算作为前提。完整声明、构建与实际证明依赖见 [形式化状态](FORMALIZATION_STATUS.md)。

**路线负责人：Codex（OpenAI）；AI 作者：Codex 与 Claude（Anthropic）。** Claude 负责传统路线，并提供本路线早期 76 格版本的审阅；Codex 负责本路线的研究、实现、形式化与论文。人类作者身份暂不填写。[AI 使用声明](AI_USE.md)逐项说明实际贡献和审查范围。

## 论文、证明与研究记录

| 阅读目的 | 入口 |
|---|---|
| 完整阅读当前证明 | [新论文 PDF](paper/current/main.pdf) · [十二章源码与构建说明](paper/current/README.md) |
| 查清七项前提与可信性依据 | [输入登记表](documentation/inputs.md) · [机器可读登记](documentation/inputs.json) |
| 从论文查到 Lean 定理 | [证明导读](documentation/blueprint/README.md) · [逐条对应表](documentation/blueprint/theorem_map.md) |
| 查看最终 Lean 定理 | [FinalResult.lean](lean/LegendreK6/FinalResult.lean) |
| 理解探索、失败与方法迭代 | [研究档案](research-history/README.md) · [阶段回顾](research-history/chronological_review.md) |
| 重现计算与内核验证 | [复现说明](REPRODUCING.md) · [审计索引](audit/README.md) |
| 审核本次整理 | [审核入口](REVIEW_THIS_RELEASE.md) · [文件散列清单](MANIFEST.json) |

论文从实际 ζ 零点和七项输入开始，依次推导梯形权、密度分层、整数矩证书、连续平移、有限高度 RH 重加权、无限尾部与整数下端，最后拼接为全范围结论。当前远段采用梯形权；早期多项式权稿件及证书保留在[历史论文入口](paper/README.md)。

## 七项外部输入

| 输入 | 内容 | 证据类别 |
|---|---|---|
| H1 | QRH(7/8) | 按研究约定接受 OpenAI 官方发布；本库不重建上游证明 |
| H2 | CS v2 推论 1 及指定十二行常数 | 固定版本预印本依赖；独立上游审查另行进行 |
| H3 | Rosser 零点计数界 | 已发表文献输入 |
| H4 | 积分显式公式 | 已发表公式的精确特化，接受稿已核对 |
| H5 | 高度 3×10¹² 内的 RH | 已发表严格计算结果 |
| H6 | CHJII 短区间显式公式 | 已发表；所用预印本版本已核对，期刊定稿比对待补 |
| H7 | CHL 素数短区间十二行 | 原文及勘误已发表；修订表匹配，舍入见证问题另有记录 |

选择接受 H1，是为了在 [OpenAI 官方 quasi-RH 发布](https://github.com/openai/math/tree/main/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026) 的基础上研究短区间素数问题。固定提交与所用 ζ 结论见输入登记。上述“接受”“已发表”“Lean 已验证”分别说明不同证据；七项命题仍完整保留在最终定理类型中。

## 覆盖如何连接

令 x=n⁶、L=log x。整数下端覆盖 n≤1,242,317,999,994；它与 L≥167 的解析覆盖重叠。下中段为 [167,178.75]，上中段为 [178.75,400]，远段为 [400,700]，尾部为 L≥700。远段与尾部先给出长度 4x³⁄⁴ 的区间，随后嵌入六次幂所需区间。

三个最终形式化预算上界分别为 **0.939772、0.966283、0.450022**，均严格小于 1。旧 94 格证明的“CS 系数统一上调 6%”结果保留原适用范围，不能直接推广为新下中段证明的灵敏度定理。

k=4 仍是阶段研究目标，k=3 是长期目标；本次全范围定理为 k=6。档案中的其他 k 候选保留当时的输入与验证状态。

本次整理先供本地审核，尚未推送。原创代码采用 0BSD，原创文字与数据采用 CC0-1.0，详见[本路线许可](LICENSE)；第三方来源保留原许可与引用。
