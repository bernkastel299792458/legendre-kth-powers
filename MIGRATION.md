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

## Commit identifiers changed on 2026-11-07 / 2026-11-07 提交号变更

At the project owner's request, the author and committer records of the
commits below were set to `bernkastel299792458` and `main` was force-pushed.
Commit dates, messages and file trees are unchanged; only the commit
identifiers changed. Commits before `ed1f97e` (up to and including `2448d78`)
keep their identifiers.

Audit records written before this change, such as the QRH `audit/*.json`
files and `routes/qrh/LOG.md`, cite the old identifiers. They were not
rewritten. Use this table, and check that the tree hash of the new commit
equals the recorded state.

| Old commit | New commit | Tree (identical before and after) |
|---|---|---|
| `b1d00a8b1fd6d6db085e928e7161677f44e9a7a2` | `ed1f97edf6d4f02d2407f56de0173c8a24d6481d` | `5b0c16e641d1d20fced8bca11235bc24a2c9e231` |
| `a136d6749bf81ce48c095f83dc7ebd55053db00a` | `765442d578d301db3e5004e2d845ff469f19382b` | `eb67d35e5ab0e6401983669dee80fc71ae89d325` |
| `9087d46124fa69cab9d3d95f8b4bafc8cc2546f7` | `f8dbb530603fdda219453bc61eb763ff5ff45537` | `df745ff1512d69f3a9825f2904666db28cbf9a3c` |
| `37b7fbcbb3b900b86600996642eccdfe465d8fdd` | `117a5262d00d4a0896a931f94779b09233cdd96c` | `df66a39b91c2946d479edb848d72f13a33f04458` |
| `f6891ed3837fcb8892e41f80c3b34128c36d48fb` | `698d174387e059fcf8c6d43728ecb11cbb4d0dba` | `8ae93f5370f935d044357cd7c476b02019e85705` |
| `f1cda3360b965236434c48ad2bca4120fedfc4b1` | `0f95f74f796d8e0a70a1acfd5659e28114ed985b` | `f2a3d7132005245acf434a8e719f450983a9c1c4` |
| `b534aa6c0b32378e84c4b133f0ac852b844a64c8` | `7e0ed305f2f04fdd1f983254ca6426202955cafc` | `e48182f27a48daf84e3f2f2438c82e49f09cb217` |
| `57139a8504caef7f16d49a8a37c08d07c1c7f3d7` | `ecc0195f28b1ac6148a989edec991665a071ecb9` | `2e720cad743ce934c38b1adaaa58458ef7e03486` |
| `365b855085939b915a410e59c6b448e75013681f` | `2b8ab58ab3aad004788368e57b77c87d24f654ca` | `ebad0445f3fbe77b75e355d68733dab5c76c7d1a` |

应项目发起人要求，上表中提交的作者与提交者记录改为 `bernkastel299792458`，并强制推送了 `main`。
提交时间、说明和文件树都没有变，只有提交号变了；`2448d78` 及更早的提交号不变。
此前写成的审计记录（例如 QRH 的 `audit/*.json` 和 `routes/qrh/LOG.md`）仍引用旧提交号，没有改写；
请按上表换算，并核对新提交的树哈希与记录一致。

