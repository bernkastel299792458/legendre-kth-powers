# QRH 路线阅读与审查入口

当前成果是七项明确输入下，对每个整数 `n≥1` 存在素数 `n⁶<p<n⁶+6n⁵<(n+1)⁶` 的完整下游证明。建议按以下路径阅读。

| 读者任务 | 材料 |
|---|---|
| 从头理解完整数学证明 | [当前主论文](../paper/current/main.pdf)，[章节源码](../paper/current/README.md) |
| 判断七个外部输入及其来源 | [输入登记](inputs.md)，[精确机器记录](inputs.json) |
| 对照纸面证明和 Lean | [证明结构图](blueprint/README.md)，[声明对应表](blueprint/theorem_map.md) |
| 查看实际最终命题 | [FinalResult.lean](../lean/LegendreK6/FinalResult.lean)，[完整定理参数与依赖输出](../audit/builds/final-20261106/final_dependencies.txt) |
| 重新运行证明和计算 | [复现说明](../REPRODUCING.md) |
| 理解方法如何形成 | [研究历史](../research-history/README.md)，[迭代综述](../research-history/chronological_review.md) |
| 判断本次整理是否就绪 | [本地审阅清单](../REVIEW_THIS_RELEASE.md)，[整理验证记录](../audit/archive_review_2026-11-06.json) |
| 查看作者及审阅职责 | [AI 使用声明](../AI_USE.md)，[项目作者分工](../../../AUTHORS.md) |

当前论文采用最终 Lean 中的梯形权、整数矩和连续传播证明。历史原稿的多项式远段、逐单元认证和旧敏感性结果保留在各自版本中；当前状态不要求读者自行拼接旧稿与补充稿。

## 当前结果与资料状态

“输入已发表”“来源版本已核对”“常数可严格重放”“本库具有上游 Lean 证明”分别登记。它们不能被单一可信性标签替代。当前七项输入均是最终定理的外部参数；本项目自己的区间估计、数值预算和拼接结论均已供给证明。

原始文献 PDF 和作者代码下载保留在本机忽略目录；公开包提供来源链接、定位和散列，不将第三方材料改称项目原创。旧研究快照可能保留当时的路径和判断，具体适用范围由历史索引说明。
