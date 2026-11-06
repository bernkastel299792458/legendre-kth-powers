# QRH 路线：相邻四次幂之间的素数

本目录研究在 **所有非平凡 ζ 零点满足 Re(ρ)≤7/8** 的工作假设下，证明所有整数 n≥1 的 `(n^4,(n+1)^4)` 中存在素数。

- 近期目标：k=4 的全范围证明。
- 长期目标：k=3。
- 不要求依次完成 k=7、6、5；共用框架同步测试，选择有价值的中间结果。
- 本目录与 `../legendre_k67` 的传统路线独立；不修改或运行其活跃研究代码。

**当前状态：研究进行中，尚未证明全范围 k=4。**

**公开审查入口（2026-11-06）：** [GitHub 的 conditional-k6 发布包](https://github.com/bernkastel299792458/legendre-kth-powers/tree/main/routes/qrh)；当前本地发布入口见 [QRH 路线](../.publication/legendre-kth-powers/routes/qrh/README.md)；本目录 `proof/` 保留此前冻结版本。共同 AI 作者为 Claude 与 Codex，Codex 负责 QRH，Claude 负责传统；详见 [工作区协议](../RESEARCH_PROTOCOL.md)。全套四模块数值证书复算及现有46个Lean模块编译已通过。**端到端Lean形式化尚未完成**；具体完成项、实际定理前提及缺口见 [形式化状态](proof/FORMALIZATION_STATUS.md)。新包原创代码0BSD、原创论文/数据CC0，保留仓库传统路线原有许可。

**2026-11-06修订：k=6全范围条件性证明稿及本地证书核验已完成。** 定理显式假设 **H1：QRH(7/8)** 和 **H2：Chourasiya–Simonič 的 arXiv:2507.15184v2 推论1及表1所用常数成立**，另列明辅助文献输入。H2按预印本输入处理，本项目未独立重证它。在这些前提下，得到每个整数n≥1的`n^6<p<(n+1)^6`。加密后的94个中段单元最坏上界约0.939736，余量至少6.0264%；固定公式下三列CS常数同时上调6%仍通过全链检查。

见[自洽稿件](manuscript/K6_conditional_primes.md)、[证明入口](research/K6_PROOF.md)、[统一核验结果](results/k6_verification_summary.json)、[对Claude审阅的逐项答复](review/Response_to_Claude_K6_2026-11-06.md)。本地代理及Claude审阅均属AI复核，尚不能称为外部专家同行评议。这项结果不消除下述k=4缺口。

第五轮理论推进：下端仍覆盖所有整数`n≤1904041788883`；重新计算高高度密度常数后，远段覆盖降至所有整数`n≥e^(181/2)`，即`n≥e^90.5`。下端不依赖QRH或CS密度假设；新远段明确依赖QRH(7/8)、固定CS v2的Theorem 1与Corollary 5、原Table 1第一行、有限高度RH及经典输入。CS仍作为预印本前提，本项目没有独立重证。以L=4logn表示，保守剩余缺口为`113.1<L<362`。全范围k=4仍未完成。

[第五轮高高度密度证明](theory_round5/PROOF.md) · [第四轮结果与双对话分工](research/SESSION_2026-11-06_ROUND4.md) · [第三轮结果](research/SESSION_2026-11-06_ROUND3.md) · [第二轮结果](research/SESSION_2026-11-06_ROUND2.md) · [首轮记录](research/SESSION_2026-11-06.md) · [复算说明](RUNBOOK.md) · [统一核验结果](results/verification_summary.json)

第五轮转向远端突破：已建立[待证密度引理 D8 足够闭合全范围的归约](research/K4_DENSITY_TARGET_ROUND5.md)，完整条件预算小于0.959，并完成解析单调比较与独立复核。**D8 本身尚未证明，实际覆盖不变。** 同时给出仅在有限实部/高度盒改善两次对数损失、可望把远端推到L≈150的阶段靶点；反事实数值不是新证书。详见[第五轮研究决策](research/SESSION_2026-11-06_ROUND5.md)。

入口：

1. [科研路线](ROADMAP.md)
2. [按时间记录的研究日志](LOG.md)
3. [输入、来源与证据等级](research/INPUTS.md)
4. [平滑实验的数学说明](research/SMOOTH_MODEL.md)
5. `code/`：独立实现；`results/`：原始结果与复核记录。

当前最短证明链为[原下端覆盖](research/LOWER_RANGE.md)、[带限权下端延伸](research/K4_BANDLIMITED_ROUND3.md)、[Selberg下端延伸](research/K4_SELBERG_ROUND4.md)、[L≥362的高高度密度推论](theory_round5/PROOF.md)。同时保留并重放[L≥372的旧单调比较](research/K4_MONOTONE_ROUND3.md)、[372–375段](research/K4_ROUND3_CERTIFICATE.md)、[375–400段](research/SMOOTH_EXTENSION.md)、[400–700段](research/SMOOTH_CERTIFICATE.md)与[旧CS无限尾部](research/TAIL_BOUND_CS.md)，作为另一条远段证明链。旧FKS尾部保留为历史模块。内部交叉复核及其实际范围见各审阅记录，不是外部专家同行评议。

原有两份历史总结及 Visser PDF 保留原样。它们是资料快照，不能代替当前研究状态；特别是 k=67 的后续状态不由本目录认证。

## 结果等级

- **EXPLORATORY**：普通浮点积分/参数搜索，仅用于选择候选估计。
- **VERIFIED_NUMERIC**：针对明确数学不等式的整数或 Arb 检查；仍依赖列出的解析输入。
- **CONDITIONAL_LEMMA**：有文字推导、适用域和必要数值核验的局部结论，条件包括 QRH 或所引定理。
- **FULL_K4**：有限范围、中间范围和无限尾部全部无缝覆盖，且有独立复核。当前未达到。

不能把采样点上的 δ<1 写成整个区间的证明，不能把有限区间证书外推至无穷，也不能把错误界失败解释为猜想反例。
