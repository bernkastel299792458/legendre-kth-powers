# A short fourth-moment bound for the moving Riemann–Siegel endpoint

Write \(D_y(t)=\sum_{n\le y}n^{-1/2-it}\), \(y(t)=\sqrt{t/(2\pi)}\). Fix \(C>J>0\), \(y_0=\lfloor y(C)\rfloor\). We bound
\[
 \left(\frac12\int_{C-J}^{C+J}|D_{y(t)}(t)-D_{y_0}(t)|^4\,dt\right)^{1/4}.
\]
The lower and upper time halves involve disjoint integer shells. On the first half their union is contained in \([\lfloor y(C-J)\rfloor+1,y_0]\), on the second in \([y_0+1,\lfloor y(C+J)\rfloor]\). Dropping an endpoint of measure zero does not affect the integrals.

For a shell of consecutive positive integers \([a,b]\), let \(k=b-a,\ n=k+1\), \(r_m=\#\{(i,j)\in[a,b]^2:ij=m\}\) and \(E=\sum r_m^2\). The diagonal and permutation solutions of the product equation give \(2n^2-n\). In every other solution write the two product pairs as \((gr,hs)\) and \((gs,hr)\) with \((r,s)=1\). Up to exchange \(r>s\) and \(g\ne h\). Then \(r,s\le k\) by comparing \(gr,hr\), and \(g,h\le k\) by comparing the two multiples of \(g\) and of \(h\). All four indices are at most \(k^2\), so no extra solutions are possible when \(a>k^2\). Otherwise \(r\ge\lceil a/k\rceil\). From \(gs\ge a,gr\le b\) follows \(r-s\le rk/b\). With \(r,s\) fixed, both \(g,h\) must lie in an interval of length at most \(k/r\). Discarding coprimality thus gives the integer upper bound
\[
 E\le 2n^2-n+
 2\sum_{\max(2,\lceil a/k\rceil)\le r\le k}
 \lfloor rk/b\rfloor\lfloor k/r\rfloor(1+\lfloor k/r\rfloor).
\]

Expand the fourth power on one time half before integrating. For each ordered quadruple the time when all its indices occur is one interval, since the moving cutoff is monotone. Equal products contribute at most \(J E/a^2\). For two different products \(m,m'\), the absolute integral including their coefficient is bounded by
\[
 \min\left(\frac{J}{a^2},\frac{2(b/a)^2}{|m-m'|}\right).
\]
Indeed \(|\log(m/m')|\ge|m-m'|/\max(m,m')\) and \(\sqrt{mm'}\ge a^2\). At each positive shift \(l\), Cauchy gives \(\sum_m r_m r_{m+l}\le E\). The whole half integral is therefore bounded by
\[
 E\left(\frac{J}{a^2}+2\sum_{l=1}^{b^2-a^2}
          \min\left(\frac{J}{a^2},\frac{2(b/a)^2}{l}\right)\right).
\]
The program splits this last sum at an integer and bounds the harmonic remainder by an integral. The two half integrals are averaged before taking the fourth root. The earlier pointwise estimate and the present fourth norm can be compared at every window.

For \(H=3\,000\,175\,332\,800,\ C=H+D/2,\ J=1.01D\), the new upper bound is below 117.643 at \(D=10^{10}\) and below 245.536 at \(D=4\cdot10^{10}\). The corresponding pointwise majorants are approximately 444.149 and 2514.159. At \(D=10^9\) the pointwise bound is smaller. Multiplication by the two bounded small Euler factors and addition of the Riemann–Siegel remainder belong to the full fourth-moment computation. [Arb calculation](prefix_fourth.py)

~~~sh
python -B round5/low/prefix_fourth.py
~~~

2026-11-20. Joint project AI authors are Claude and Codex. Codex derived the shell energy and moving endpoint bounds.
