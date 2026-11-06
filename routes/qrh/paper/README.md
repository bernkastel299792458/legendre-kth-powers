# 论文源码

manuscript.md 是可读中文稿，保留全部证明公式、常数表和计算证据范围。main.tex 由 build_tex.py 生成，用于 XeLaTeX 排版。references.bib 提供相同文献的 BibTeX 记录；main.tex 内置参考文献，因此其编译不依赖另跑 BibTeX。

从本目录运行：

    python -X utf8 build_tex.py
    xelatex -interaction=nonstopmode -halt-on-error main.tex
    xelatex -interaction=nonstopmode -halt-on-error main.tex

需要支持中文的 XeLaTeX / TeX Live，含 ctex、Fandol、amsmath、longtable、fvextra、hyperref 和 xurl。第二遍用于更新目录与交叉引用。PDF 是否成功生成与实际排版检查记录，以发布包 audit 中的构建记录为准。

编辑数学正文时先改 manuscript.md，再运行 build_tex.py。该脚本只作排版转换，不计算证书，不改变数学数据。改变数学陈述时应相应重新核验源码、证书与引用；不要将 TeX 编译成功等同于数学正确。

原稿明确承认 H1：QRH(7/8) 与 H2：CS v2 推论1及指定常数，另列经典文献输入。
原稿第11节保留当时的形式化范围，不代表后续版本的状态。当前实际使用的证明方法、
七项明确输入及新增推导见[形式化补充稿](lean_formalization_addendum.md)；
构建验收状态见[FORMALIZATION_STATUS.md](../FORMALIZATION_STATUS.md)及其对应记录。
新远段采用梯形权，原多项式稿件与证书继续保留。人类署名、单位、邮箱暂不填写；
原稿 AI 使用声明在第12节，后续实现与审查范围另见[AI_USE.md](../AI_USE.md)。
