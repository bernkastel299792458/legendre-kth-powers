# 论文与版本

当前完整论文是 **[《相邻六次幂之间的素数：显式条件证明及 Lean 形式化》](current/main.pdf)**。它由十二章正文、版本附录和参考文献组成，从七项精确输入推导最终全范围结论，对应已验收的实际 Lean 证明。

- [当前论文源码及构建说明](current/README.md)
- [七项输入及来源登记](../documentation/inputs.md)
- [论文—Lean 对应表](../documentation/blueprint/theorem_map.md)
- [研究过程与原始档案](../research-history/README.md)
- [形式化验收范围](../FORMALIZATION_STATUS.md)

## 保留的早期稿件

[原中文稿](manuscript.md)、[原 PDF](main.pdf)、[原 TeX](main.tex) 和 [原参考文献](references.bib) 按原字节保留，记录数值认证阶段的证明，包含后来被新的梯形远段替代的多项式权方法。原稿第 11 节反映当时尚未完成形式化的阶段，不代表当前状态。

[形式化补充稿](lean_formalization_addendum.md) 记录 M1—M3 完成后的方法变更；新十二章论文将这些推导组织为自洽正文。历史原稿不再作为当前稿的编辑源。

如需复现历史排版，可在本目录运行 `python -X utf8 build_tex.py` 再用支持 ctex/Fandol 的 XeLaTeX 编译两次。这会重写历史 TeX，不应在核对冻结清单前运行。新稿使用独立的 [current/build.py](current/build.py)，不会覆盖旧稿。
