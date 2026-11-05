"""Dependency-free SVG plots (matplotlib is not installed here).
  out/requirement_bands.svg : weakest admissible ZFR factor s per height band (re-optimised, rigorous)
  out/fixed_thresholds.svg  : per-piece thresholds of Z1 / Z2 with the certificates' own parameters
Usage: python -I plot_svg.py"""
import os, sys; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))  # works under python -I
import csv
from math import log10

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, 'out')


class SVG:
    def __init__(self, w=900, h=420, ml=70, mr=20, mt=40, mb=55):
        self.w, self.h, self.ml, self.mr, self.mt, self.mb = w, h, ml, mr, mt, mb
        self.items = []

    def axes(self, x0, x1, y0, y1, xlog=False, ylog=False):
        self.x0, self.x1, self.y0, self.y1, self.xlog, self.ylog = x0, x1, y0, y1, xlog, ylog

    def X(self, x):
        f = (log10(x) - log10(self.x0)) / (log10(self.x1) - log10(self.x0)) if self.xlog else (x - self.x0) / (self.x1 - self.x0)
        return self.ml + f * (self.w - self.ml - self.mr)

    def Y(self, y):
        f = (log10(y) - log10(self.y0)) / (log10(self.y1) - log10(self.y0)) if self.ylog else (y - self.y0) / (self.y1 - self.y0)
        return self.h - self.mb - f * (self.h - self.mt - self.mb)

    def add(self, s):
        self.items.append(s)

    def line(self, pts, color='#1f5fa8', width=1.6, dash=None):
        d = ' '.join(f"{self.X(x):.1f},{self.Y(y):.1f}" for x, y in pts)
        da = f' stroke-dasharray="{dash}"' if dash else ''
        self.add(f'<polyline fill="none" stroke="{color}" stroke-width="{width}"{da} points="{d}"/>')

    def rect(self, x0, x1, y0, y1, color, op=0.15):
        X0, X1, Y0, Y1 = self.X(x0), self.X(x1), self.Y(y1), self.Y(y0)
        self.add(f'<rect x="{X0:.1f}" y="{Y0:.1f}" width="{X1-X0:.1f}" height="{Y1-Y0:.1f}" fill="{color}" fill-opacity="{op}"/>')

    def text(self, x, y, s, size=12, anchor='start', color='#222'):
        self.add(f'<text x="{x:.1f}" y="{y:.1f}" font-size="{size}" text-anchor="{anchor}" fill="{color}" '
                 f'font-family="sans-serif">{s}</text>')

    def frame(self, xt, yt, xlabel, ylabel, title):
        L, R, T, B = self.ml, self.w - self.mr, self.mt, self.h - self.mb
        self.add(f'<rect x="{L}" y="{T}" width="{R-L}" height="{B-T}" fill="none" stroke="#444"/>')
        for x in xt:
            X = self.X(x)
            self.add(f'<line x1="{X:.1f}" y1="{B}" x2="{X:.1f}" y2="{B+5}" stroke="#444"/>')
            self.text(X, B + 18, f"{x:g}", 11, 'middle')
        for y in yt:
            Y = self.Y(y)
            self.add(f'<line x1="{L-5}" y1="{Y:.1f}" x2="{L}" y2="{Y:.1f}" stroke="#444"/>')
            self.add(f'<line x1="{L}" y1="{Y:.1f}" x2="{R}" y2="{Y:.1f}" stroke="#ddd"/>')
            self.text(L - 8, Y + 4, f"{y:g}", 11, 'end')
        self.text((L + R) / 2, self.h - 12, xlabel, 13, 'middle')
        self.add(f'<text x="16" y="{(T+B)/2:.1f}" font-size="13" text-anchor="middle" font-family="sans-serif" '
                 f'transform="rotate(-90 16 {(T+B)/2:.1f})">{ylabel}</text>')
        self.text(L, 22, title, 14)

    def save(self, fn):
        with open(fn, 'w', encoding='utf-8') as f:
            f.write(f'<svg xmlns="http://www.w3.org/2000/svg" width="{self.w}" height="{self.h}" '
                    f'viewBox="0 0 {self.w} {self.h}"><rect width="100%" height="100%" fill="white"/>')
            f.write('\n'.join(self.items))
            f.write('</svg>')


def bands_plot():
    fn = os.path.join(OUT, 'bands.csv')
    if not os.path.exists(fn):
        return
    rows = list(csv.DictReader(open(fn)))
    s = SVG()
    s.axes(28, 1.6e6, 0.0, 1.05, xlog=True)
    col = {'Z1': '#d95f02', 'Z2': '#1b9e77', 'Z3': '#7570b3'}
    for r in rows:
        v0, v1 = float(r['v_lo']), float(r['v_hi'])
        s.rect(v0, v1, 0, 1.05, col[r['active_constant']], 0.10)
        if r['s_ok'] not in ('', 'None'):
            y = float(r['s_ok'])
            s.line([(v0, y), (v1, y)], color='#111', width=2.4)
    s.line([(28, 1), (1.6e6, 1)], color='#999', dash='4 3', width=1)
    s.frame([30, 55, 100, 300, 1000, 1e4, 1e5, 1e6], [0, 0.2, 0.4, 0.6, 0.8, 1.0],
            'v = log t (height band, log scale)', 'smallest admissible factor s',
            'k = 67: how far the zero-free width may be scaled down on each band (shading: Z1 / Z2 / Z3 active)')
    s.text(s.X(33), s.Y(0.08), 'classical (Z1)', 12, 'start', col['Z1'])
    s.text(s.X(120), s.Y(0.08), 'Littlewood (Z2)', 12, 'start', col['Z2'])
    s.text(s.X(7e5), s.Y(0.08), 'VK', 12, 'start', col['Z3'])
    s.save(os.path.join(OUT, 'requirement_bands.svg'))


def fixed_plot():
    s = SVG(h=440)
    s.axes(2000, 1.2e4, 4.8, 30, xlog=True, ylog=True)
    for fam, color in (('Z1', '#d95f02'), ('Z2', '#1b9e77')):
        fn = os.path.join(OUT, f'fixed_{fam}.csv')
        if not os.path.exists(fn):
            continue
        pts = []
        for r in csv.DictReader(open(fn)):
            La, Lb = float(r['L_a']), float(r['L_b'])
            if r['status'] == 'thr' and La < 1.2e4:
                pts.append(((La + Lb) / 2, min(30, float(r['thr_ok']))))
        pts.sort()
        if pts:
            s.line(pts, color=color, width=1.2)
            s.text(s.X(pts[0][0]) + 4, s.Y(pts[0][1]) - 6, fam, 12, 'start', color)
    s.line([(2000, 4.896), (1.2e4, 4.896)], color='#d95f02', dash='4 3', width=1)
    s.line([(2000, 19.62), (1.2e4, 19.62)], color='#1b9e77', dash='4 3', width=1)
    s.frame([2000, 3000, 4000, 5000, 7000, 10000], [4.896, 6, 8, 10, 15, 19.62, 25],
            'L = log x', 'weakest constant keeping this piece', 'Per-piece thresholds with the certificates\' own parameters (dashed: values used)')
    s.save(os.path.join(OUT, 'fixed_thresholds.svg'))


if __name__ == '__main__':
    bands_plot()
    fixed_plot()
    print('written:', [f for f in os.listdir(OUT) if f.endswith('.svg')])
