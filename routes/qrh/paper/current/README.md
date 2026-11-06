# 当前论文：本地审阅稿

**《相邻六次幂之间的素数：显式条件证明及 Lean 形式化》**

[阅读全文 PDF](main.pdf)。人类作者身份暂未填写；AI 贡献按 Claude 与 Codex 的实际分工记录。此版先交项目发起人审核，尚未推送为新的公开版本。

这是按照最终实际 Lean 证明重新组织的完整主稿。它从七项精确输入出发，依次证明梯形权估计、实际零点预算、内核数值证书、连续覆盖、无限尾部与整数下段，再拼接所有正整数的结论。旧稿和补充稿继续保存在上一层，不作为这份论文的替代章节。

## 正文与来源

唯一正文源是 [main.tex](main.tex) 及其 [sections](sections/) 内的章节；参考文献为 [references.bib](references.bib)。PDF 由这些文件编译，不同时维护另一份可独立修改的 Markdown 正文。

- [七项输入及证据登记](../../documentation/inputs.md)
- [论文与 Lean 对照](../../documentation/blueprint/README.md)
- [研究历史与版本迭代](../../research-history/README.md)
- [正式化范围与验收](../../FORMALIZATION_STATUS.md)
- [本次整理的审阅入口](../../REVIEW_THIS_RELEASE.md)

## 排版复现

使用 Tectonic（本机核验版本记录在构建报告），在当前目录执行：

```sh
python build.py
python build.py --check
```

Tectonic 不在 PATH 时使用 `--engine /absolute/path/to/tectonic`。构建所需 ctex/Fandol 等 TeX 包由 Tectonic 的正常包获取机制提供。临时文件保存于路线目录的 `tmp/paper-builds/`，最终 PDF 保存在当前目录。

[构建报告](build_report.json)绑定所有章节、书目、构建脚本和 PDF 的 SHA-256；[视觉检查报告](../../audit/current_paper_visual_review.json)另记录页面检查。排版成功、视觉检查、数学审查与 Lean 内核验证分别记录，不能相互替代。

参考文献样式 `plainurl.bst` 随包提供，保留 URL/DOI 输出，避免编译时临时下载样式失败。其[来源、完整发行包和许可](third_party/urlbst/PROVENANCE.md)单独列明；构建脚本会拒绝缺少书目或未解析引用的输出。
