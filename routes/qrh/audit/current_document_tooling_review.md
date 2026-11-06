# 当前文档工具与引用元数据审查

日期：2026-11-06。

审查范围：

- code/build_reading_map.py；
- paper/current/build.py；
- CITATION.cff 的字段结构与许可元数据含义。

以上路径相对于 routes/qrh/。本轮只新增本报告，没有修改被审脚本或论文，也没有重编共享 PDF、安装全局包或扩展数学测试。

## 审查角色边界

审查者为 Codex 协作代理 /root/credibility_classical，不是这两份构建脚本的编写者。但此前负责从官方 CTAN 取得 plainurl.bst、核查其许可及完成隔离排版测试，并建议将实际使用的 bst 纳入 PDF 来源哈希和防止静默书目失败。因此，这是一轮额外的代码审读，不能称为对整个构建方案完全无参与的盲审。

本代理还主写论文第 4–7 节。本报告仅涉及文档工具与元数据，不重复声称数学证明的独立审查。

## 结论

两份脚本在当前文档结构和实际标记用法下未发现阻断性问题：生成链接存在，引用映射能复算，缺失书目和缺失被引条目的拒绝分支位于替换正式 PDF 之前，实际 bst 与源文件均被纳入 SHA-256 绑定。

发现一处需要修正的引用元数据问题：CITATION.cff 的许可证数组表达“任选一个许可证”，不能表达当前项目的按组件分别许可。已向主会话报告；详见第 4 节。

## 1. 检查版本

| 文件 | 审查时 SHA-256 |
|---|---|
| code/build_reading_map.py | efde9f1740bc206be64b8be73e2b7d233221e9225067005b1523b6ddff72deb2 |
| paper/current/build.py | 892f550d947ae11b3d27ad307b5372b0a60379840d98497f4504affeeeaa0d55 |
| CITATION.cff（发现问题的版本） | e71d6cd09b7e55f8db9e11eaf35aee552a074308bab0101d4290bf266ede19ec |

当前 PDF 的 SHA-256 为：
500fa769a0933774b677264fab06ecfa403cdc2bb67575f6e485f4ddaa3b446f。

## 2. 阅读映射的路径、声明与引用验证

已执行：

    python routes/qrh/code/build_reading_map.py --check

结果：

    READING_MAP_VERIFIED 150

额外只读核对结果：

- 13 个章节对应当前 main.tex 实际包含的 13 个章节文件；
- 150 个引用映射涉及 63 个不同 Lean 文件；
- 每个记录行号都落在实际声明行，而非注释中的同名字符串；
- 生成的 theorem_map.md 中 164 个相对文件链接全部解析到存在的文件；
- 从 documentation/blueprint/ 出发的 ../../ 路径正确返回路线目录；
- 章节和 Lean 文件的 SHA-256 被写入 JSON；--check 重新生成后按 UTF-8 字节比较两个发布输出；
- TeX 重复标签、未定义的 ref/eqref/pageref、缺失的 cite/nocite 键分别进入错误集合，而不是静默忽略。

这里的声明匹配是文本级的文件/短名称定位，代码及生成文档已经明确它不是 Lean 解析器，也不证明人类文字与 Lean 命题语义等价。当前 150 项没有发现由这一边界造成的错误定位。本轮没有为假设性的未来标记格式扩展测试或修改实现。

## 3. PDF、书目与 SHA 绑定

已执行：

    python routes/qrh/paper/current/build.py --check

结果：

    PAPER_SOURCE_PDF_BINDING_PASS 17

审读确认：

1. 构建使用新的、带时间戳的临时输出目录，不在验证前覆盖已保存的正式 PDF。
2. Tectonic 非零退出码直接拒绝继续。
3. main.bbl 不存在或为空时拒绝继续，因此先前“找不到 plainurl.bst 却得到不完整 PDF”的失败不会被仅凭引擎退出码接受。
4. 从 main.aux 提取实际被引键，并与 main.bbl 的 bibitem 键集合比较；缺少被引条目时拒绝继续。
5. 检查最终 TeX 日志中的未定义交叉引用警告。
6. 在复制正式 PDF 之前重新计算所有受管源文件哈希；构建期间源文件发生变化则拒绝。
7. main.tex、references.bib、plainurl.bst、build.py 和 13 个章节，共 17 个源文件被绑定到报告；报告另记录正式 PDF 哈希。
8. --check 同时比较当前 17 个源文件哈希集合和实际 PDF 哈希，不是仅检查报告文件存在。

当前实际构建的 main.aux 有 14 个被引键，main.bbl 有 14 个条目，差集为空；main.blg 明确使用 plainurl.bst 和 references.bib，未报告 BibTeX 错误。

上述守卫证明的是当前所声明的书目完整性与来源绑定，不应描述成对每条参考文献书目信息的真伪审查或对所有可能 BibTeX 警告的通用验证器。当前文献字段与来源状态仍由对应文献审计负责。

## 4. 实质发现：CFF 许可证数组的语义

问题版本在 CITATION.cff 使用：

    license:
      - 0BSD
      - CC0-1.0

CFF 1.2.0 的官方 schema 在 definitions.license 中明确规定，多许可证数组按 OR 解释。它表示同一被引用作品可以任选列出的许可证，不表示“代码用第一种、论文和数据用第二种”。因此，这份元数据与本路线现行的组件许可边界不一致，也没有表达已随附的第三方样式材料保留原许可。

依据：[CFF 1.2.0 官方 schema](https://raw.githubusercontent.com/citation-file-format/citation-file-format/1.2.0/schema.json)，definitions.license；字段说明另见[官方 schema guide](https://github.com/citation-file-format/citation-file-format/blob/main/schema-guide.md#license)。

建议的最小修正：删去这个不能准确表示组件关系的 license 数组，在 message 或 abstract 中说明许可按组件适用，并指向实际许可索引。不要为了让数组成立而默默把第三方材料改为 CC0/0BSD。此处是机器可读元数据与仓库既有声明的一致性问题，不要求修改论文数学或重编 PDF。

其它已读字段未发现结构问题：所需 authors、cff-version、message、title 均存在；type: software 合法；authors 中只有 name 的对象属于 schema 允许的 entity 形式，不需要虚构人类姓和名。后者与显式 AI 归属说明相容。

本轮没有安装 YAML 或 JSON Schema 验证包；CFF 的结论来自对文件与官方 schema 的定向人工核对，不声称已通过完整自动 schema 验证。

## 5. 审查限制

本报告不重跑 Lean 或证书，不验证七个外部输入，不声称哈希能代替数学审阅，也不重新检查全部 57 页视觉排版。PDF 第 15–28 页的实际视觉记录另见 current_paper_visual_15_28.json。

没有提出与正确性无关的代码风格修改，没有扩大测试矩阵，也没有推送或提交。

## 6. 修正复核：已解决

2026-11-06 再次读取修正后的 routes/qrh/CITATION.cff，并计算其 SHA-256。原先表示可任选许可证的 license 数组已经删除；message 现在明确说明原创代码使用 0BSD，原创文字与数据使用 CC0-1.0，第三方文件保留各自许可，并指向 LICENSE。所需的 authors、cff-version、message、title 字段仍然存在。

第 4 节发现的组件许可表达问题已解决。修正版 CITATION.cff 的 SHA-256 为：

    82d3fa5264a174eb0cf037da23b1906f90f04a0678c725d52da6c633da84c351

本次仅复核这一项修正，没有改动正文、PDF 或构建脚本，也没有扩大为完整自动 CFF schema 验证；前述审查角色边界和限制继续适用。
