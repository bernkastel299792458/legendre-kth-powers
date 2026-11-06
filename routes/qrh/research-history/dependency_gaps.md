# 快照的缺失依赖与原链接清单

本清单描述本次选择边界，不改写历史文件。快照用于保存研究证据，不是一个依赖齐全的独立运行包；本次没有执行旧程序。

静态扫描确认 144 处相对链接的文件或目录仍在快照内；另登记 34 处未随快照满足的链接，涉及 23 个不同目标。3 处 `logT`/`log T` 数学表达式经人工识别，不计为文件链接。完整逐处来源见 [dependency_gaps.json](dependency_gaps.json)。

## 选择性不收录的依赖

- 旧 `proof/`、`.lake`、编译缓存与第三方 PDF/源代码：明确排除，不能从此快照单独重建原发布包。
- `computation_branch/`、`algorithm_only/`：属于另行工作的活跃范围，不复制、不运行，也不在本档案认证其结果。
- `manuscript/`：未纳入此次研究数据白名单。历史链接保留；当前稿件与独立旧稿归档由仓库的其他入口管理。
- `review/` 的已有审阅：通过当前仓库审阅目录索引，不重复复制。旧76格归档中的Claude审稿也同样处理。
- `code/requirements.txt`：不在用户指定的 MD/PY/JSON/CSV 范围内。原文提及的运行环境照原样保留，未安装或验证。
- Python静态导入发现外部依赖：`flint`, `numpy`, `scipy`。依赖包不随快照分发。

## 原76格归档的特殊限制

旧 `archive/k6_before_claude_revision_2026-11-06/` 原本就是选定文件的历史保存，而不是完整项目树。它内部有指向未存在于该旧目录的研究文档、辅助脚本或证书的链接。此次保持这种历史状态，没有把后来版本补入旧目录冒充当时版本。根层同时保存了较新的研究文件，读者可作版本比较，但这不证明缺失旧依赖与新文件相同。

旧归档的原 `manifest.json` 也保持原字节；其列出的Claude审稿在本次快照中不重复保存，原稿可在 [当前审阅档案](../audit/source_reviews/Claude_K6_proof_review_2026-11-06.md)查阅。新快照的权威字节清单是本目录 [snapshot_manifest.json](snapshot_manifest.json)。

## 未满足的相对目标

| 原相对目标（以 Legendre_k8 为基准） | 处数 | 原路径状态 / 处理 |
|---|---:|---|
| `../.publication/legendre-kth-powers/routes/qrh/README.md` | 1 | 超出所选源根目录，未复制 |
| `../RESEARCH_PROTOCOL.md` | 1 | 超出所选源根目录，未复制 |
| `archive/k6_before_claude_revision_2026-11-06/LOG.md` | 1 | 原相对路径本身未找到；不擅自修复 |
| `archive/k6_before_claude_revision_2026-11-06/ROADMAP.md` | 1 | 原相对路径本身未找到；不擅自修复 |
| `archive/k6_before_claude_revision_2026-11-06/research/K6_DENSITY_INPUT.md` | 1 | 原相对路径本身未找到；不擅自修复 |
| `archive/k6_before_claude_revision_2026-11-06/research/K6_KERNEL_EXPLORATION.md` | 1 | 原相对路径本身未找到；不擅自修复 |
| `archive/k6_before_claude_revision_2026-11-06/research/LOWER_RANGE.md` | 1 | 原相对路径本身未找到；不擅自修复 |
| `archive/k6_before_claude_revision_2026-11-06/research/LOWER_RANGE_K6.md` | 1 | 原相对路径本身未找到；不擅自修复 |
| `archive/k6_before_claude_revision_2026-11-06/research/LOWER_RANGE_K6_REVIEW.md` | 2 | 原相对路径本身未找到；不擅自修复 |
| `archive/k6_before_claude_revision_2026-11-06/research/SESSION_2026-11-06.md` | 1 | 原相对路径本身未找到；不擅自修复 |
| `archive/k6_before_claude_revision_2026-11-06/research/SESSION_2026-11-06_ROUND2.md` | 1 | 原相对路径本身未找到；不擅自修复 |
| `archive/k6_before_claude_revision_2026-11-06/research/SMOOTH_CERTIFICATE.md` | 2 | 原相对路径本身未找到；不擅自修复 |
| `archive/k6_before_claude_revision_2026-11-06/research/SMOOTH_EXTENSION.md` | 1 | 原相对路径本身未找到；不擅自修复 |
| `archive/k6_before_claude_revision_2026-11-06/research/SMOOTH_MODEL.md` | 1 | 原相对路径本身未找到；不擅自修复 |
| `archive/k6_before_claude_revision_2026-11-06/research/TAIL_BOUND_CS.md` | 2 | 原相对路径本身未找到；不擅自修复 |
| `archive/k6_before_claude_revision_2026-11-06/results/lower_range_k6_certificate.json` | 1 | 原相对路径本身未找到；不擅自修复 |
| `archive/k6_before_claude_revision_2026-11-06/results/verification_summary.json` | 1 | 原相对路径本身未找到；不擅自修复 |
| `manuscript/K6_conditional_primes.md` | 2 | 原路径存在，但不在本次选择内 |
| `proof/FORMALIZATION_STATUS.md` | 2 | 原路径存在，但不在本次选择内 |
| `review/Claude_K6_proof_review_2026-11-06.md` | 4 | 原路径存在，但不在本次选择内；[已有仓库审阅](../audit/source_reviews/Claude_K6_proof_review_2026-11-06.md) |
| `review/K6_manuscript_revision_review_2026-11-06.md` | 1 | 原路径存在，但不在本次选择内；[已有仓库审阅](../audit/source_reviews/K6_manuscript_revision_review_2026-11-06.md) |
| `review/K6_revision_numeric_audit_2026-11-06.md` | 4 | 原路径存在，但不在本次选择内；[已有仓库审阅](../audit/source_reviews/K6_revision_numeric_audit_2026-11-06.md) |
| `review/Response_to_Claude_K6_2026-11-06.md` | 1 | 原路径存在，但不在本次选择内；[已有仓库审阅](../audit/source_reviews/Response_to_Claude_K6_2026-11-06.md) |

## 扫描范围

脚本只扫描普通 Markdown 内联相对链接和 Python 静态导入。HTML 链接、引用式链接、嵌套括号、锚点存在性、动态 `runpy` 或 `Path` 拼接并未被完整解析；程序中出现的路径不保证都已枚举。因此清单不是“已证明所有旧脚本可直接运行”的声明。历史文字没有为配合扫描而修改。

本清单记录归档时发现的缺失材料与版本取舍；该次扫描没有推送、补下载第三方内容或运行旧数学程序。审查包的后续公开状态见[发布记录](../audit/publication_2026-11-06.json)，不据此改写原始快照。
