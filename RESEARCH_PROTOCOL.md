# Research collaboration protocol / 科研协作协议

Effective date / 生效日期：2026-11-06。依据：项目发起人明确指定的两路线分工。

## 1. 路线与负责人

| 路线 | 负责人 | 工作目录 | 研究前提 |
|---|---|---|---|
| 传统显式估计 | **Claude** | `routes/traditional/` | 不使用 QRH 假设；文献输入及其评审状态逐条列明 |
| QRH(7/8) 及其推论 | **Codex** | `routes/qrh/` | 接受 QRH(7/8) 作为明确上游输入；CS v2 等其他输入单独列明 |

项目共同 AI 作者为 **Claude 与 Codex**，具体贡献按 [AUTHORS.md](AUTHORS.md) 记录。
路线以方法和前提划分，不以 k=6、k=67 等阶段目标命名。定理、证书及 Lean 命名空间中的
指数属于数学对象或历史标识，可以保留，不能因整理目录而改写其数学含义。

## 2. QRH 路线的起点

采用 QRH(7/8) 的依据是 OpenAI 在 [openai/math](https://github.com/openai/math)
公开的 [2026-09-30 证明论文](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/README.md)
和 [Family 003 专项 Lean 材料](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/docs/003.md)。
本项目把 ζ 非平凡零点实部不超过 7/8 作为明确输入，研究后续的素数区间推论。
上游已有专项形式化；本项目尚未独立重建该上游证明，也不能借此声称自己的完整推论已形式化。

## 3. 并行工作的边界

1. 各负责人默认主导本路线的研究、代码、证书、稿件、日志和形式化。
2. 跨路线阅读和复核可以进行；反馈须说明检查范围、是否参与原实现及依据版本。
   不能把同一实现者的自检称为完全独立审阅。
3. 对方路线的实质性数学或实现修改，应有明确任务授权或工作交接。用户的新指令优先。
   本次用户已授权 Codex 执行全仓目录迁移、链接/CI 修复及共同作者署名；这不是传统研究职责转移。
4. 根 README、作者声明、协议、许可说明及 `.github/` 是共同维护区。
   执行已授权任务所必需的更新可直接完成，并记录影响范围；不增加重复确认流程。
5. 不在同一个 Git 索引上并行暂存、提交或变基。每个写入者使用自己的 checkout/worktree，
   提交前检查状态，只纳入本任务修改；发布前 fetch，整合已进入远端的更改，不强推覆盖他人历史。
6. 不重置、清理或搬动另一个会话的活跃工作目录。旧本地研究目录作为历史工作区保留，
   将新成果映射到对应路线后再发布。具体本地位置记录在工作区协议中，不写入公共数学产物。

## 4. 证据、日志与发布

- 明确区分探索计算、严格区间证书、书面条件证明、已编译的 Lean 引理与端到端形式化。
- 全量形式化要求精确外部前提到结论的完整连接。`sorry` 检查、标准公理审计和成功编译
  都不能隐藏 theorem 参数中的未证局部结论。
- 每次实质修改记录动机、输入版本、适用范围、验证命令和结果；失败与撤回记录不删除。
- 数值证书与脚本散列绑定时，不为美化目录或注释而改动冻结数学文件。必要的版本更改另行记录并复算。
- 历史审阅和对话保留当时内容；用迁移表解释旧路径，不伪造原审阅者对新版本的认可。
- QRH 路线更新发布文件后刷新并验证 `MANIFEST.json`。使用 Python 3.12.10 重放当前冻结证书。
- 数学改动运行相应验证；纯目录迁移至少检查路径、文件散列、必要的构建和复算。
  CI 的结果必须和对应提交、路线及验证范围一起报告。
- 许可证按目录适用：传统路线默认 Apache-2.0；QRH 原创代码 0BSD，原创论文/文档/数据 CC0。
  不重新许可第三方内容。

## English summary

Claude leads `routes/traditional/`; Codex leads `routes/qrh/`. Both are named
AI authors with their actual contributions distinguished. QRH is adopted
because of OpenAI's released 7/8 manuscript and formalization materials;
the project's own downstream obligations remain explicit.

Use separate checkouts/worktrees for simultaneous writes, preserve audit
history and pinned certificate bytes, and update shared documentation within
the authorized task. User instructions take precedence over this protocol.
The current repository reorganization is explicitly authorized; it does not
transfer responsibility for traditional-route research to Codex.
