"""Render this project's Markdown paper to a standalone XeLaTeX source.

The converter handles the deliberately restricted Markdown used in manuscript.md.
It preserves mathematical source verbatim and requires no external document tool.
It does not compile TeX or change mathematical data.
"""
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
BT = chr(96)

SOURCE_KEYS = {
    "2507.15184": "CSv2",
    "2004.09765": "PT",
    "2103.05986": "CHL",
    "2402.04272": "CHJ",
    "1509.00864": "SW",
    "03005-1": "Dusart",
    "2371291": "Rosser",
    "2610.20058": "Visser",
    "arblib.org": "Arb",
    "1611.02831": "Arb",
    "978-3-030-79876-5_37": "Lean",
    "9780521397896": "Ingham",
    "mathlib4/blob/": "Mathlib",
}

def escape(s):
    mapping = {
        "\\": r"\textbackslash{}",
        "&": r"\&", "%": r"\%", "$": r"\$", "#": r"\#",
        "_": r"\_", "{": r"\{", "}": r"\}",
        "~": r"\textasciitilde{}", "^": r"\textasciicircum{}",
        "ζ": r"\(\zeta\)",
        "→": r"\(\to\)",
    }
    return "".join(mapping.get(c, c) for c in s)

def code(s):
    if re.fullmatch(r"[0-9a-f]{64}", s):
        parts = [s[i:i + 16] for i in range(0, 64, 16)]
        return r"{\ttfamily\scriptsize " + r"\allowbreak{}".join(parts) + "}"
    return r"\nolinkurl{" + s + "}"

def inline(s, cite=True):
    # Each protected unit is parsed before escaping ordinary prose.
    patt = re.compile(
        r"\\\(.*?\\\)|" + BT + r"[^" + BT + r"]+" + BT
        + r"|\[[^\]]+\]\([^)]+\)|\*\*.+?\*\*|\*[^*]+\*"
    )
    out, pos = [], 0
    for m in patt.finditer(s):
        out.append(escape(s[pos:m.start()]))
        part = m.group()
        if part.startswith(r"\("):
            out.append(part)
        elif part.startswith(BT):
            out.append(code(part[1:-1]))
        elif part.startswith("["):
            label, url = re.match(r"\[([^\]]+)\]\(([^)]+)\)", part).groups()
            out.append(r"\href{" + url.replace("%", r"\%").replace("#", r"\#")
                       + "}{" + inline(label, cite=False) + "}")
            if cite and url.startswith("http"):
                for fragment, key in SOURCE_KEYS.items():
                    if fragment in url:
                        out.append(r"~\cite{" + key + "}")
                        break
        elif part.startswith("**"):
            out.append(r"\textbf{" + inline(part[2:-2], cite=cite) + "}")
        else:
            out.append(r"\emph{" + inline(part[1:-1], cite=cite) + "}")
        pos = m.end()
    out.append(escape(s[pos:]))
    return "".join(out)

def table(rows):
    cells = [[x.strip() for x in line.strip().strip("|").split("|")]
             for line in rows]
    cells = [row for row in cells if not all(re.fullmatch(r":?-+:?", x)
                                           for x in row)]
    n = len(cells[0])
    if any(len(row) != n for row in cells):
        raise ValueError("Unbalanced table")
    widths = ([0.36, 0.60] if n == 2 else
              [0.34, 0.34, 0.28] if n == 3 else
              [0.28, 0.20, 0.21, 0.27] if n == 4 else [0.96/n]*n)
    widths = [w * 0.92 for w in widths]
    spec = "".join(r">{\raggedright\arraybackslash}p{" + f"{w:.4f}"
                   + r"\textwidth}" for w in widths)
    out = [r"\begingroup\small\setlength{\tabcolsep}{3pt}",
           r"\begin{longtable}{" + spec + "}", r"\toprule",
           " & ".join(inline(x) for x in cells[0]) + r" \\",
           r"\midrule\endfirsthead", r"\toprule",
           " & ".join(inline(x) for x in cells[0]) + r" \\",
           r"\midrule\endhead", r"\bottomrule\endfoot"]
    out += [" & ".join(inline(x) for x in row) + r" \\" for row in cells[1:]]
    out += [r"\end{longtable}", r"\endgroup"]
    return "\n".join(out)

def convert(text):
    lines = text.splitlines()
    out, i = [], 0
    while i < len(lines):
        s = lines[i]
        if s.startswith("# "):
            i += 1
            continue
        if s == "## 摘要":
            out.append(r"\begin{abstract}")
            i += 1
            while i < len(lines) and not lines[i].startswith("## "):
                if lines[i].strip() == r"\[":
                    j = i + 1
                    while lines[j].strip() != r"\]":
                        j += 1
                    out.append("\n".join(lines[i:j+1]))
                    i = j + 1
                else:
                    out.append(inline(lines[i]))
                    i += 1
            out.append(r"\end{abstract}")
            out.append(r"\noindent\textbf{关键词：}素数短区间；零点密度；准黎曼假设；区间算术；计算辅助证明。")
            out.append(r"\tableofcontents\newpage")
            continue
        if s == "## 参考文献":
            out.append(r"\begingroup\small\begin{thebibliography}{99}")
            keys = ["CSv2", "PT", "Ingham", "CHL", "CHJ", "SW",
                    "Dusart", "Rosser", "Visser", "Arb", "Lean", "Mathlib"]
            j = 0
            i += 1
            while i < len(lines):
                line = lines[i]
                if re.match(r"^\d+\. ", line):
                    body = re.sub(r"^\d+\. ", "", line)
                    out.append(r"\bibitem{" + keys[j] + "} "
                               + inline(body, cite=False))
                    j += 1
                i += 1
            if j != len(keys):
                raise ValueError(f"Expected {len(keys)} references; got {j}")
            out.append(r"\end{thebibliography}\endgroup")
            continue
        if s.startswith("## "):
            title = re.sub(r"^\d+\.\s*", "", s[3:])
            out.append(r"\section{" + inline(title, cite=False) + "}")
            i += 1
            continue
        if s.startswith("### "):
            title = re.sub(r"^\d+\.\d+\s*", "", s[4:])
            out.append(r"\subsection{" + inline(title, cite=False) + "}")
            i += 1
            continue
        if s.strip() == r"\[":
            j = i + 1
            while j < len(lines) and lines[j].strip() != r"\]":
                j += 1
            if j == len(lines):
                raise ValueError("Unclosed display math")
            out.append("\n".join(lines[i:j+1]))
            i = j + 1
            continue
        if s.startswith(BT * 3):
            j = i + 1
            while j < len(lines) and not lines[j].startswith(BT * 3):
                j += 1
            body = lines[i+1:j]
            if len(body) == 1 and re.fullmatch("[0-9a-f]{64}", body[0]):
                out.append(r"\begin{quote}" + code(body[0]) + r"\end{quote}")
            else:
                out += [r"\begin{Verbatim}[fontsize=\small,breaklines=true]",
                        "\n".join(body), r"\end{Verbatim}"]
            i = j + 1
            continue
        if s.startswith("|") and s.rstrip().endswith("|"):
            j = i + 1
            while j < len(lines) and lines[j].startswith("|") and lines[j].rstrip().endswith("|"):
                j += 1
            out.append(table(lines[i:j]))
            i = j
            continue
        if re.match(r"^(\d+\. |- )", s):
            numbered = bool(re.match(r"^\d+\. ", s))
            env = "enumerate" if numbered else "itemize"
            pattern = r"^\d+\. " if numbered else r"^- "
            out.append(r"\begin{" + env + "}")
            while i < len(lines) and re.match(pattern, lines[i]):
                out.append(r"\item " + inline(re.sub(pattern, "", lines[i])))
                i += 1
            out.append(r"\end{" + env + "}")
            continue
        out.append(inline(s))
        i += 1
    return "\n".join(out)

PREAMBLE = r"""% !TEX program = xelatex
% Generated from manuscript.md by build_tex.py; edit manuscript.md first.
\documentclass[UTF8,zihao=-4,fontset=fandol]{ctexart}
\usepackage[a4paper,margin=23mm]{geometry}
\usepackage{amsmath,amssymb,mathtools,booktabs,longtable,array}
\usepackage{fvextra}
\usepackage{xcolor}
\usepackage[unicode,colorlinks=true,linkcolor=blue!45!black,citecolor=blue!45!black,urlcolor=blue!45!black]{hyperref}
\usepackage{xurl}
\allowdisplaybreaks
\setlength{\parindent}{2em}
\setlength{\parskip}{0.25em}
\emergencystretch=3em
\hypersetup{pdftitle={QRH(7/8) 与显式零点密度假设下相邻六次幂之间的素数},pdfauthor={Claude; Codex}}
\title{QRH(7/8) 与显式零点密度假设下\\相邻六次幂之间的素数}
\author{Claude（传统路线负责人；本路线早期审阅）\\[0.3em]Codex（QRH 路线负责人；本稿主要研究与实现）}
\date{公开审查稿，2026年11月6日}
\begin{document}
\maketitle
"""

def main():
    text = (HERE / "manuscript.md").read_text(encoding="utf-8")
    tex = PREAMBLE + convert(text) + "\n\\end{document}\n"
    (HERE / "main.tex").write_text(tex, encoding="utf-8", newline="\n")
    print(f"Wrote main.tex ({len(tex)} characters)")

if __name__ == "__main__":
    main()
