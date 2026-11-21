# 相邻 k 次幂之间的素数

[English](README.md) | **简体中文**

**作者：bernkastel299792458、Claude 与 Codex。** bernkastel299792458 为项目发起人；Claude 负责传统路线，Codex 负责 QRH(7/8) 路线。
[作者与贡献](AUTHORS.md) · [协作协议](RESEARCH_PROTOCOL.md)

本仓库研究：对哪些整数 k，**每个整数 n ≥ 1** 的开区间
`(n^k, (n+1)^k)` 中都存在素数。项目包含两条研究路线，分别采用不同的数学前提，
各有自己的审查包和验证记录。

## 路线 A 的四次幂结果 · 2026-11-21

我们提出了一份以 QRH(7/8) 为前提的计算机辅助证明稿，主张在所需辅助解析估计成立时，对每个正整数 $n$ 都存在素数 $p$ 满足

$$
n^4 < p < n^4+4n^3 < (n+1)^4.
$$

小端由 44,721 个素数见证和九条已发表的区间估计覆盖。令 $L=4\log n$，中间的 682 个闭格与 $L\ge167.8$ 的无穷尾接合。此前最难的 $116\le L\le120$ 使用旋转检测多项式保留零点的余弦相位，40 格的完整误差上界均低于 0.974019，判据要求小于 1。数值证书已从冻结副本重放。

[四次幂证明稿与假设](routes/qrh/research/k4_20261120/PROOF_K4.md) · [逐格重放记录](routes/qrh/research/k4_20261120/REPLAY_K4.txt) · [核验程序](routes/qrh/research/k4_20261120/verify_k4.py) · [输入表重建](routes/qrh/research/k4_20261120/INPUTS_K4.md)

## 经典 RH 动态与三次幂推论

本项目跟踪 Levent Alpöge 与 Claude 发布的 Lean 形式化及其独立内核核验。**当经典 RH 成立时，对每个正整数 $n$，相邻立方 $n^3$ 与 $(n+1)^3$ 之间都存在素数。** 这一推论来自 Dudek 的显式短区间定理，小整数情形可逐项验证。[原始公告、核验日志与完整推导](docs/rh-tracking.md)

## 成果总览

下表每项结论均覆盖**所有正整数 n**，并以对应文献输入和本项目稿件中的新论证为基础。

| 研究路线 | 当前报告的成果 | 主要前提 | 审查入口 |
|---|---|---|---|
| **A. QRH(7/8)** | **k = 4** | 以 QRH(7/8) 为前提的证明稿，辅助输入清单和部分误差论证待修订 | [四次幂证明](routes/qrh/research/k4_20261120/PROOF_K4.md) |
| **A. 假定 QRH(7/8) 成立的路线** | 固定指数 **k = 6** | **七项明确输入**，包括 QRH(7/8)、CS **arXiv:2507.15184v2** 推论 1 及指定表格行；见[完整陈述](routes/qrh/documentation/inputs.md) | [QRH 路线审查包](routes/qrh/README.md) · [中文论文 PDF](routes/qrh/paper/current/main.pdf) |
| B. 传统显式估计路线 | 所有整数 k ≥ 37（v5，进行中） | 经评审的文献输入，加上本项目自己的引理；不假定 QRH。Arb 证书链，尚无合并的 v5 论文。早先 v4 的 k ≥ 70 / 74 目前不成立 | [传统路线入口](routes/traditional/README.md) |

“仅用经评审文献输入”描述的是所用文献的状态，不表示本项目的新证明已经通过同行评审。
两条路线的数学前提不同，比较指数时必须同时说明这些前提。

## 路线 A：假定 QRH(7/8) 成立

本路线以 [OpenAI 官方 quasi-RH 发布](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/README.md)
为研究起点，将其中 ζ 非平凡零点的 7/8 实部界作为明确输入。
[Family 003](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/docs/003.md)
说明上游形式化范围，本项目研究其素数短区间推论。

### 四次幂 · 当前的条件性证明稿

稿件要证明，对每个正整数 $n$，开区间 $(n^4,n^4+4n^3)$ 中都有素数。这个区间包含在相邻四次幂之间。QRH(7/8) 给出 ζ 函数非平凡零点实部的上界；要推出区间内有素数，还需控制显式公式中零点和高次素数幂的贡献。

令 $L=4\log n$。小端通过素数见证和已发表的区间估计处理，中段以 682 个闭区间接合，最后一段从 $L=167.8$ 延伸到无穷。在原有缺口 $116\le L\le120$，计算保留零点项的余弦相位，40 格的总误差上界均低于 0.974019，满足小于 1 的判据。数值证书已重放；完整条件性结论仍取决于辅助解析估计的适用范围及误差论证。[四次幂证明稿](routes/qrh/research/k4_20261120/PROOF_K4.md) · [逐格计算记录](routes/qrh/research/k4_20261120/REPLAY_K4.txt)

### 六次幂 · 七项输入下的 Lean 定理

在 **QRH(7/8)、CS v2、Rosser、积分显式公式、有限高度 RH、CHJII、CHL 七项精确输入**下，
对每个整数 n≥1，存在素数 `n^6 < p < n^6+6n^5 < (n+1)^6`。
[输入登记表](routes/qrh/documentation/inputs.md)列出命题、版本和证据依据。
CS v2 仍是预印本依赖，全部七项仍明确保留在最终 Lean 定理中。

完整下游定理 `sixth_powers_from_named_inputs` 已通过 **241 个模块**的全新输出目录重建和对应依赖审计。
本项目的解析区间与数值预算均有实际证明，不再列作额外前提。详见[形式化范围](routes/qrh/FORMALIZATION_STATUS.md)。

整理后的入口包括[新十二章中文论文](routes/qrh/paper/current/main.pdf)、
[论文—Lean 导读](routes/qrh/documentation/blueprint/README.md)、
[中英文路线主页](routes/qrh/README.zh-CN.md)和[研究档案](routes/qrh/research-history/README.md)。
论文完整讲解最终采用的梯形权与连续平移证明；原多项式稿件及证书保留为历史版本。
旧稿的 CS 系数 6% 灵敏度结果保留原适用范围。

[数学审查入口](routes/qrh/REVIEW_THIS_RELEASE.md)汇总完整 k=6 论文、前提、Lean 源码与核验记录。

## 路线 B：传统显式估计

### 结论与方法

**进展（v5，2026-11-07）：** Arb 证书链给出所有整数 k ≥ 37 的结论，依据是经评审的文献输入和本项目自己的引理；合并论文在准备中。见 [v5 工作区](routes/traditional/work/README.md)。

早先 v4 的 k ≥ 70 / 74 目前不成立：它用到了 Bellotti 零点密度估计印刷版的 Table 2，本项目发现该文 §4 有计数缺口。这是本项目的判断，未经原作者确认。以下内容描述 v4。

这条路线结合显式零点自由区域、混合零点密度估计、平滑显式公式、有限区间证书和解析无限尾部。
它**不假定 QRH(7/8)**。

k ≥ 70 版本使用预印本常数 4.896。k ≥ 74 版本使用经评审的常数 5.558691。
两者还使用 21.233、54.004 及论文列明的其他输入。

### 证据与验证范围

数值区间由 Arb 证书覆盖。Lean 在**假定列明的解析估计和证书结论成立**时，
检查各区间的逻辑拼接；它没有证明这些解析估计或 Arb 计算本身。
详见[审查清单](routes/traditional/proof/REVIEW_CHECKLIST.md)、
[数值重放记录](routes/traditional/proof/certificates/verify_all_output.txt)和
[Lean 覆盖范围](routes/traditional/proof/README.md#lean-证明了什么)。

文献核对和待审事项分别记录在
[SOURCES.md](routes/traditional/SOURCES.md)和[输入核查](routes/traditional/proof/input_verification/)中。
其中 Bellotti 的表格目前核对的是 arXiv v2，与期刊印刷版表格逐项比对仍是待审事项。

**早先的 k ≥ 67 结论已经撤回。** 项目核查在所需常数 19.62 的博士论文证明中发现了算术问题。
这一判断是本项目对原文的理解，尚不是经原作者确认的勘误。
参见
[撤回结论的历史证书](routes/traditional/proof/certificates/withdrawn_k67/README.md)。
Lean 项目保留的历史名称 `LegendreK67` 不代表当前仍声称证明了 k = 67。

## 阅读、复现与审查

四次幂证明的完整重放命令如下。环境版本见[证明稿](routes/qrh/research/k4_20261120/PROOF_K4.md)。

```sh
python -B -X utf8 routes/qrh/research/k4_20261120/verify_k4.py
```

| 目的 | 传统路线 | QRH 路线 |
|---|---|---|
| 阅读论证 | [英文论文](routes/traditional/proof/manuscript.md) | [当前论文](routes/qrh/paper/current/main.pdf) · [证明导读](routes/qrh/documentation/blueprint/README.md) |
| 检查输入 | [论文第 3 节](routes/traditional/proof/manuscript.md) · [文献来源](routes/traditional/SOURCES.md) | [七项输入](routes/qrh/documentation/inputs.md) · [BibTeX](routes/qrh/paper/current/references.bib) |
| 复现计算 | [v5 证书](routes/traditional/work/v5/README.md) · [v4 审查包复算说明](routes/traditional/proof/README.md#如何复核) | [复现说明](routes/qrh/REPRODUCING.md) |
| 理解 Lean 范围 | [逻辑拼接的范围](routes/traditional/proof/README.md#lean-证明了什么) | [准确结论与验收证据](routes/qrh/FORMALIZATION_STATUS.md) |

**传统路线数值重放**，从仓库根目录运行：

```sh
python -m pip install -r routes/traditional/proof/code/requirements.txt
python routes/traditional/proof/code/verify_all.py
```

**六次幂数值重放**，使用 **Python 3.12.10**，从仓库根目录运行。
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
| **Claude：传统路线** | 完成文献整理、推导、代码、证书、Lean 逻辑拼接和论文。 |
| **Codex：QRH 路线** | 完成条件性论证、加密证书、Lean 模块、论文和复现包。 |

QRH 论文 PDF 的作者页尚未按新署名重新编译；单位和邮箱暂未填写。

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
| `routes/traditional/code/`、`routes/traditional/docs/`、`routes/traditional/results/` | 传统路线早期工作文件，包括已替换的常数和已撤回的设定；当前结论以 `routes/traditional/proof/` 为准 | [Apache-2.0](LICENSE) |
| `routes/qrh/` | QRH 路线论文、证书、代码、Lean、范围声明、审计记录和发布哈希 | 原创代码 **0BSD**；原创论文、文档及数据 **CC0-1.0**。见[包内许可](routes/qrh/LICENSE)。 |

根目录 [LICENSE](LICENSE) 给出默认 Apache-2.0 条款，条件性研究包单独声明自己的许可范围。
第三方作品和依赖保留原有许可证；所引论文通过链接提供，不随本仓库重新分发。
