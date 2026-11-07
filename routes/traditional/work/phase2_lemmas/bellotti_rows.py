"""Bellotti (arXiv:2405.12545v2) Appendix A tables, parsed from work/ref/bel_v2.txt.
rows[i] = dict(L0, L1 (log T0, log T1), alpha0, C, B, b1, b2, u, x, v, w, d4, d5, c1..c5)."""
import re, math, os
HERE = os.path.dirname(os.path.abspath(__file__))
REF = os.path.join(HERE, "..", "ref", "bel_v2.txt")
BS = chr(92)  # backslash


def _num(s):
    s = s.strip().replace(BS + "cdot", "*").replace(" ", "")
    if s.startswith(BS + "exp(") and s.endswith(")"):
        return ("exp", float(s[5:-1]))
    if s == "3*10^{12}":
        return ("exp", math.log(3e12))
    m = re.fullmatch(r"([0-9.]+)\*10\^\{(\d+)\}", s)
    if m:
        return float(m.group(1)) * 10 ** int(m.group(2))
    return float(s)


def _parse():
    txt = open(REF, encoding="utf-8", errors="replace").read()

    def table(a, b, ncols, skip_head):
        i = txt.index(a); j = txt.index(b, i)
        vals = re.findall(r"\$([^$]*)\$", txt[i:j])[skip_head:]
        return [[_num(v) for v in vals[k:k + ncols]] for k in range(0, len(vals) - ncols + 1, ncols)]

    t2 = table("Table 2. Values of constants", "Table 3.", 5, 6)    # T0 T1 a0 C B
    t3 = table("Table 3. Values of constants", "Table 4.", 5, 6)    # T0 T1 a0 b1 b2
    t4 = None
    t5 = table("Table 5. Values of constants", "Table 6.", 9, 10)    # T0 T1 d11 d12 d21 d22 d3 d4 d5
    t6 = table("Table 6. Values of constants", "References", 7, 8)  # T0 T1 c1..c5
    return t2, t3, t4, t5, t6


def _parse4():
    # Table 4 values u x v w are not in $...$; parse lines after "Table 4."
    txt = open(REF, encoding="utf-8", errors="replace").read()
    i = txt.index("Table 4. Choice of parameters"); j = txt.index("Table 5.", i)
    lines = [l.strip().rstrip("|").strip() for l in txt[i:j].splitlines()]
    toks = [l for l in lines if l and l not in ("u", "x", "v", "w")]
    out = []; k = 0
    toks = [t for t in toks if (t.startswith("$") and "T_" not in t) or re.fullmatch(r"[0-9.]+", t)]
    while k < len(toks):
        if toks[k].startswith("$") and k + 5 < len(toks) and toks[k + 1].startswith("$"):
            T0 = _num(toks[k].strip("$")); T1 = _num(toks[k + 1].strip("$"))
            vals = [float(toks[k + 2 + q].strip("$")) for q in range(4)]
            out.append([T0, T1] + vals); k += 6
        else:
            k += 1
    return out


def _rows():
    t2, t3, _, t5, t6 = _parse()
    t4 = _parse4()
    rows = []
    for r2, r3, r4, r5, r6 in zip(t2, t3, t4, t5, t6):
        L0 = r2[0][1]; L1 = r2[1][1]
        for r in (r3, r4, r5, r6):
            assert abs(r[0][1] - L0) < 1e-9, (r, L0)
        rows.append(dict(L0=L0, L1=L1, alpha0=r2[2], C=r2[3], B=r2[4], b1=r3[3], b2=r3[4],
                         u=r4[2], x=r4[3], v=r4[4], w=r4[5], d4=r5[7], d5=r5[8],
                         c1=r6[2], c2=r6[3], c3=r6[4], c4=r6[5], c5=r6[6]))
    return rows


rows = _rows()


def find(L):
    for r in rows:
        if r["L0"] <= L <= r["L1"]:
            return r
    raise KeyError(L)


if __name__ == "__main__":
    print(len(rows), "rows")
    for r in rows:
        print(f"[{r['L0']:.2f},{r['L1']:.1f}] a0={r['alpha0']} C={r['C']} B={r['B']} u={r['u']} x={r['x']} "
              f"v={r['v']} w={r['w']} d4={r['d4']} d5={r['d5']} b1={r['b1']} b2={r['b2']} c1={r['c1']} c5={r['c5']}")
