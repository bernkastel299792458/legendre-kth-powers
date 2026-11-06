# Route-based repository layout / 按研究路线整理仓库

Date: 2026-11-06. Previous layout: commit
[`10116cd`](https://github.com/bernkastel299792458/legendre-kth-powers/tree/10116cdf508dad9cd5a3aec53e0bf0ccf1ac816a).

The repository is organized by mathematical approach, not by the exponent of
the current result. **Claude leads the traditional route; Codex leads the
QRH(7/8) route. Both are named AI authors with their actual roles stated.**

## Path map

| Previous repository path | Current path |
|---|---|
| `conditional-k6/` | `routes/qrh/` |
| `proof/LegendreK67/` | `routes/traditional/proof/lean/` |
| Other `proof/` contents | `routes/traditional/proof/` |
| `code/`, `docs/`, `results/`, `review/` | The corresponding directory under `routes/traditional/` |
| `ROADMAP.md`, `LOG.md`, `SOURCES.md` | The corresponding file under `routes/traditional/` |
| `.github/workflows/conditional-k6.yml` | `.github/workflows/qrh.yml` |

Root `README.md`, `README.zh-CN.md`, `AUTHORS.md`, `RESEARCH_PROTOCOL.md`,
`AGENTS.md`, and `CLAUDE.md` describe the whole project. Root `LICENSE` remains
the default Apache-2.0 license; `routes/qrh/LICENSE` retains its 0BSD/CC0 scope.

The [file-by-file migration audit](MIGRATION_AUDIT.json) accounts for all 394
previously tracked files and compares their SHA256 identifiers.

## What changes and what stays versioned

Current navigation, build instructions, CI paths, author statements, and the
QRH paper's author page have been updated. The traditional Lean project's
outer folder is `lean/`; its internal package and namespace `LegendreK67`
remain unchanged. QRH's `LegendreK6` namespace and result-specific certificate
names also remain unchanged. These identify mathematical statements or
historical implementations, not research-track directories.

The migration does not alter mathematical program, Lean-source, or certificate
bytes. It does not change proof assumptions or upgrade either route's
formalization status. The QRH manuscript adds author/role text; its mathematical
body is unchanged. Its PDF and metadata are rebuilt and its release manifest
is refreshed. Traditional manuscript edits are attribution and path updates.

Historical review reports and conversation records preserve their original
text, paths, and version hashes. A review of an older manuscript is not a
review of a later editorial revision. See the
[QRH migration note](routes/qrh/audit/MIGRATION_NOTE.md).

## Interpreting old links and local paths

Old links into `main/conditional-k6/` or `main/proof/` should use the mapping
above. For the exact originally reviewed bytes, use the corresponding commit
permalink instead. Absolute `Legendre_k8` and `legendre_k67` paths in historical
reports refer to the development machine at the time; they are not portable
public links. Missing third-party papers and external source checkouts were
not distributed before this migration and remain external dependencies.

Active local research workspaces were not moved or reset. The local workspace
protocol records their connection to the new route directories. Before pulling
this layout into an older checkout, preserve any uncommitted work and map it
to the appropriate route; do not publish an old directory layout over the new
one. See [the collaboration protocol](RESEARCH_PROTOCOL.md).

## 中文说明

仓库按 `routes/traditional/`（Claude）和 `routes/qrh/`（Codex）两条路线组织。
共同 AI 作者署名为 Claude 与 Codex，实际贡献另行注明。
目录、当前入口、构建说明、CI 和作者说明已调整，数学程序、Lean 源码与证书字节不因本次整理改变。
证明内部的 `LegendreK6`、`LegendreK67` 等名称保留；它们是数学对象或历史标识，不是新的路线分类。

历史审阅、研究对话及旧版本哈希不批量改写。其旧路径按本页映射解释，需要核对原始字节时使用旧提交链接。
本地仍被其他会话使用的工作区保持原位；更新远端布局前先保留本地未提交修改，再按对应路线整合。
本次整理没有消除任何尚未完成的形式化义务。
