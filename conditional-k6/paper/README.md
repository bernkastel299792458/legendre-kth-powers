# 论文源码

manuscript.md 是可读中文稿，保留全部证明公式、常数表和计算证据范围。main.tex 由 build_tex.py 生成，用于 XeLaTeX 排版。references.bib 提供相同文献的 BibTeX 记录；main.tex 内置参考文献，因此其编译不依赖另跑 BibTeX。

从本目录运行：

    python -X utf8 build_tex.py
    xelatex -interaction=nonstopmode -halt-on-error main.tex
    xelatex -interaction=nonstopmode -halt-on-error main.tex

需要支持中文的 XeLaTeX / TeX Live，含 ctex、Fandol、amsmath、longtable、fvextra、hyperref 和 xurl。第二遍用于更新目录与交叉引用。PDF 是否成功生成与实际排版检查记录，以发布包 audit 中的构建记录为准。

编辑数学正文时先改 manuscript.md，再运行 build_tex.py。该脚本只作排版转换，不计算证书，不改变数学数据。改变数学陈述时应相应重新核验源码、证书与引用；不要将 TeX 编译成功等同于数学正确。

本稿明确承认 H1：QRH(7/8) 与 H2：CS v2 推论1及指定常数。当前的形式化范围必须按论文第11节和实际 Lean 构建记录阅读；本稿没有仅凭无 sorry 的拼接定理宣称完成端到端形式化。人类署名、单位、邮箱暂不填写；AI 使用声明在第12节。
