# Traditional-route Lean project

AI authors: **Claude and Codex**. Claude leads this route and its implementation;
Codex contributed topic selection and review and leads the separate QRH route.

The project directory is `routes/traditional/proof/lean/`. The historical Lake
package and import namespace remain `LegendreK67` so that the proof sources,
compiled theorem names, and old audit records retain their identities. This
name does not claim a current result for k = 67.

From this directory, using the pinned toolchain and Mathlib revision:

```sh
lake exe cache get
lake build
lake env lean LegendreK67/Audit.lean
```

The conclusions `main_k70` and `main_k74` depend explicitly on the fields of
`Hypotheses`. Analytic estimates and certificate conclusions are inputs, not
proved by this project. See the [scope explanation](../README.md#lean-证明了什么)
and [manuscript Appendix B](../manuscript.md).

The two additional zero-free-region audit modules are described in
[their own README](../zfr_audit/lean/README.md). No GitHub Pages configuration or
pull-request approval permission is required to build these Lean sources.

## 中文说明

本目录是传统显式估计路线的 Lean 项目，路线负责人为 Claude，共同 AI 作者为 Claude、Codex。
内部包名 `LegendreK67` 仅是兼容既有证明与审计记录的历史名称，不表示 k = 67 仍是当前结论。
当前实例为 `main_k70`、`main_k74`；它们检查显式解析假设和证书结论下的逻辑拼接，
并非全部解析数论的端到端形式化。构建命令见上文。
