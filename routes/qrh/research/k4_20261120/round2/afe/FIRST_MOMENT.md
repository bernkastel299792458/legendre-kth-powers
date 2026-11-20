# The first moment of the sharp Möbius mollifier

Let \(H=3\cdot10^{12},\ p=7/8,\ T\ge H,\ 7/10\le\sigma\le p,\ r=2\sigma-1\).
Write \(M_X(s)=\sum_{d\le X}\mu(d)d^{-s}\) and \(f=\zeta M_X-1\).
The expansion \(|f|^2=|\zeta M_X|^2-1-2\Re f\) gives the first-moment cost
\(2|\langle f\rangle|\) for a normalized nonnegative height weight. The following
bounds compare that specific cost with the proposed scale \(X^{-r}\).

| Height average | Range of the fixed length \(X\) | Bound for \(2X^r|\langle f\rangle|\) |
|---|---|---|
| Gaussian, any center, width \(D\ge T/10\) | \(1\le X\le\min(T^p,10^{14})\) | \(1.81\cdot10^{-8}\) |
| Squared sinc, any center, same width | same | \(1.02\cdot10^{-8}\) |
| Uniform on \([A,T]\), \(10^3\le A\le T/2\) | \(1\le X\le T^p\) | \(0.162\) |

The Gaussian and squared sinc averages use the whole real height axis. The
last row handles an actual finite interval and includes both endpoint costs.
All rows are unconditional. They estimate the linear term in the variance.
The quadratic off-diagonal terms and a suitable height-weight comparison for
the zero detector are separate requirements for an application to fourth powers.

## 1. An exact formula for smooth averages

Take a center \(t_0\in\mathbb R\), let \(s_0=\sigma+it_0\), and put
\[
 K_G(s)=\exp((s-s_0)^2/D^2),\qquad
 K_F(s)=\left(\frac{\sinh((s-s_0)/D)}{(s-s_0)/D}\right)^2 .
\]
The quotients have their continuous values at zero. Their masses on the
height line are \(m_G=\sqrt\pi D,\ m_F=\pi D\). Set
\(\langle f\rangle_j=m_j^{-1}\int_{\mathbb R} f(\sigma+it)K_j(\sigma+it)\,dt\).
Let \(a_X(n)=\sum_{d\mid n,\,d\le X}\mu(d)\) for \(n\ge2\). Then
\[
 \langle f\rangle_j=
 \sum_{n\ge2}a_X(n)n^{-s_0}w_j(\log n)
 -\frac{2\pi}{m_j}M_X(1)K_j(1),
 \quad w_G(\xi)=e^{-D^2\xi^2/4},\quad
 w_F(\xi)=(1-D|\xi|/2)_+ .                                     \tag{1}
\]
Indeed shift the upward vertical line from \(\sigma\) to 2. The pole crossed
has residue \(M_X(1)K_j(1)\), with the displayed minus sign when expressing
the left integral in terms of the right integral. Both horizontal edges disappear.
For instance the first-order Euler summation formula with \(N=\lfloor |t|\rfloor\)
gives \(O((1+|t|)^{0.3}(1+\log |t|))\) for \(\zeta(c+it)\), uniformly on
\(\sigma\le c\le2,\ |t|\ge1000\). The mollifier is fixed, and \(K_F\) decays as
\(O_{D,t_0}(|t|^{-2})\) throughout this strip. On the line 2 the series for
\(f\) converges absolutely, permitting termwise integration. Translating
each entire summand back to \(\sigma\) gives the usual Fourier transforms
of the Gaussian and squared sinc. For the latter, the representation
\(\sin u/u=\tfrac12\int_{-1}^1 e^{iuy}\,dy\) yields the triangular transform.

For \(D>2/\log 2\) the squared sinc removes the entire series in (1).
For \(D\ge8\) the Gaussian series has modulus at most
\[
 2e^{-D^2(\log 2)^2/8},
\]
because \(|a_X(n)|\le d(n)\),
\(n^{2-\sigma}e^{-D^2(\log n)^2/8}\le1\), and
\(\sum_{n\ge2}d(n)n^{-2}=\zeta(2)^2-1<2\).
For the pole we use
\(|M_X(1)|\le\sqrt{2/X}\) for \(1\le X\le10^{14}\).
[Helfgott, Lemma 5.10](https://webusers.imj-prg.fr/~harald.helfgott/anglais/PartI.pdf).

Uniformly in the center, \(|K_G(1)|\le e^{1/D^2}\) and
\(|K_F(1)|\le e^{2/D}\), the latter by the integral representation of
\(\sinh z/z\). For \(X\ge1,\ X^{2\sigma-3/2}\le X^{1/4}\le T^{7/32}\).
The two normalized pole costs are therefore bounded by
\(40\sqrt{2\pi}T^{-25/32}e^{1/D^2}\) and
\(40\sqrt 2 T^{-25/32}e^{2/D}\). Adding the Gaussian series bound and
substituting \(T=H,\ D=H/10\) in the majorants proves the first two rows.

## 2. The hard-window estimate

In the rectangle with real coordinates \([\sigma,2]\) and heights \([A,T]\)
the function \(f\) is holomorphic. On its right edge,
\[
 \left|\int_A^T f(2+it)\,dt\right|
 \le 2\sum_{n\ge2}\frac{d(n)}{n^2\log n}
 \le \frac{2(\zeta(2)^2-1)}{\log 2}<5.                         \tag{2}
\]
For \(1\le Y,\ 0<c\le1\) write
\(B(Y,c)=1+\int_0^{\log Y} e^{(1-c)z}dz\).
It bounds \(\sum_{n\le Y}n^{-c}\) by the integral test. Put \(P=\sqrt T\),
\(Y=T^p\). For \(c\in[\sigma,1]\) and either horizontal edge \(t=A,T\),
\[
 |\zeta(c+it)|\le Z_T(c)=B(P,c)+P^{1-c}/c+1.205,\qquad
 |M_X(c+it)|\le M_T(c)=B(Y,c).                                  \tag{3}
\]
Indeed take \(x=y=\sqrt{t/(2\pi)}\) in the explicit approximate functional
equation. The first sum has modulus \(\le B(x,c)\); the dual sum is bounded
by \(x^{1-2c}\sum_{n\le x}n^{c-1}\le x^{1-c}/c\). The remainder is at most
\(1.205x^{-c}\) for \(t\ge10^3\), using specifically the symmetric column of
Table 2 for the approximation with \(\widetilde\chi\).
[Simonič, Corollary 1, Table 2 and equations (11)–(13)](https://arxiv.org/pdf/1910.08274).

For \(1\le c\le2\) use instead
\[
 Z_T(c)=\min(3+\log T,1+1/(c-1)),\qquad
 M_T(c)=\min(1+\log Y,1+1/(c-1)).
\]
The minimum takes its finite first entry at \(c=1\). For the first entry of
the zeta bound take \(N=\lfloor t\rfloor\) in Euler summation. The initial
sum is at most \(1+\log T\), the pole term at most \(1/t\), and the integral
remainder at most \(|c+it|N^{-c}/c\le\sqrt{t^2+4}/(t-1)\).
The sum of these last two bounds is below 2. The second entry is the
absolute-series bound for \(c>1\). At \(c=1\) either of (3) and this estimate
can be used on its respective side.

Define \(J_T(s)=\int_s^2(1+Z_T(c)M_T(c))\,dc\), with the two definitions
on their indicated ranges. By (2) and the horizontal segments,
\[
 \frac{2X^r}{T-A}\left|\int_A^T f(\sigma+it)\,dt\right|
 \le T^{pr-1}(20+8J_T(\sigma)).                                  \tag{4}
\]
This also works with arbitrary coefficients of modulus at most 1 when the
constant coefficient of \(\zeta M\) is 1.

To verify (4) on the infinite height range, let \(R=T/H,\ K=\log T/\log H\).
In \(B(T^b,c)\), change the integral variable \(z\) to \(Kz\).
For \(c\le1\), this gives
\(B(T^b,c)\le K R^{b(1-c)} B(H^b,c)\) for \(b=1/2,p\).
Thus the integrand of \(J_T(\sigma)\) on this side grows by at most
\(K^2 R^{(p+1/2)(1-\sigma)}\) relative to \(H\). For \(c>1\) each minimum
grows by at most \(K\), which gives the same majorant. The full right side
of (4) is therefore at most its value at \(H\) times
\[
 K^2 R^{-\frac12+(p-\frac12)\sigma}
 \le K^2 R^{-11/64}\le1
\]
since \(2/\log H<11/64\).

The integrands at \(H\) are decreasing on each of \([\sigma,1]\), \([1,2]\).
The [Arb verifier](check_first_moment.py) uses upper rectangle sums with
mesh \(1/20000\) for each piece. For a cell of possible \(\sigma\) it takes
the lower endpoint in the integration limit and the upper endpoint in
\(H^{p(2\sigma-1)-1}\). The largest resulting enclosure has upper bound
\(0.161785\). Reproduce using Python with python-flint:

```text
python -B check_first_moment.py
```

2026-11-20. Joint project attribution to Claude and Codex. Codex derived
and checked these first-moment estimates in the QRH workstream.
