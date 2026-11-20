# What the location mean square would need for a single fourth-power gap

In the notation of [the block proof](EXCEPTIONAL.md), ruling out even one
exception by its unit-window energy would follow from
\[
 \int_L^{L+1}|Z(c)|^2dc < (2/M)D^2 .
\]
At \(L=116\) and \(120\), \(2/M\) is respectively \(3.96202\cdot10^{-13}\)
and \(1.45755\cdot10^{-13}\). The upper bound used in the K5 column is
respectively \(1.22983\cdot10^{10}\) and \(2.37274\cdot10^{10}\) times
this one-gap threshold. The CS ratios are \(2.71732\cdot10^{11}\) and
\(4.23084\cdot10^{11}\). These are ratios of our certified upper expressions
to the sufficient threshold. Actual prime gaps need not resemble the bounds.

Already on the diagonal of the squared zero sum there is a limiting
exponent: at \(\beta=7/8\) the squared amplitude \(e^{-2(1-\beta)L}\)
equals \(e^{-L/4}\), the order of the available one-gap energy.
For a single permitted positive ordinate \(H<\gamma<H+10^8\) with
\(\beta=b=0.8748\), and its negative-height conjugate, the two diagonal
terms in the unit-block energy, divided by \(2/M\), are exactly
\[
 e^{1/4+[1/4-2(1-b)]L}|K_{1/M}(b-1+i\gamma)|^2
 \frac{1-e^{-2(1-b)}}{2(1-b)} .
\]
The same compact-tent comparison used below bounds
\(\lvert K_{1/M}\rvert\ge (1-u^2/6)^2-(e^{1/M}-1)\), where
\(u=(H+10^8)/(2M)<1\). The resulting ratios exceed 1.02193 and
1.07404 respectively. Thus a diagonal-only upper estimate allowing even
this pair already loses the one-gap test. In the actual moment, off-diagonal
cross terms can have either sign; the positive diagonal alone is not a
lower bound for that full moment.

There is also an obstruction to shrinking the location window in this
method. The following construction uses a synthetic spectrum satisfying
the location, total-count, CS-density and global K5-budget inequalities
used in the block proof. It is **not** the zero set of zeta, and the
construction is not a statement about the primality of either indicated
integer interval.

Take \(n=\lceil e^{L/4}\rceil,\ c_0=4\log n+D_0,\ D_0=2\log(1+1/n)\).
Modify the repository's existing symmetric model from
\(\texttt{Legendre_k8/research/STRUCTURAL_ROUND2.md}\), §§1–3.
Set \(H=3\,000\,175\,332\,800\), the exact published verification height,
and \(W=10^8\). Use only \(m=5\cdot10^6\)
positive-height pairs, and use \(b=0.8748\). The model begins with critical
pairs at quantiles of the Riemann–von Mangoldt main term. In the window
\((H,H+W)\) it has over \(10^8\) available double points separated by more
than \(0.4\). Selected pairs move to the nearest multiple of \(2\pi/c_0\)
and split into \(b+i\gamma_j\) and \(1-b+i\gamma_j\), with conjugates at
negative heights. The displacement is less than \(0.03\), so the count
deviation remains below 4 at modified heights. Unused pairs and low
ordinates stay on the critical line. The referenced construction supplies
the finite-height and total-count checks. Every CS bound used above
\(\sigma=1/2\) exceeds \(5.069H^{1/3}(\log H)^{7/3}>m\), so also holds.

For the precise K5 input accepted in (6) of the block proof, the right
points cost at most \(2m e^{(b-1)\lambda}\) at every \(\lambda\ge138\).
All the remaining positive ordinates have \(\beta\le1/2\) and cost at most
\[
 4e^{-\lambda/2}T_0(\log T_0+1),\qquad
 T_0=\frac{16}{\sqrt7}(1+e^{\lambda/5}/5)\le8e^{\lambda/5}.
\]
Indeed \(g_q(t)\le\min(1,T_0^2/t^2)\); integrate \(N(t)\le t\log t\)
against its negative derivative. For the count restricted above \(H\)
the same bound is valid below \(H\) since the restricted count is zero.
Both resulting bounds decrease for \(\lambda\ge138\), and their sum is
less than \(0.314\), well below the K5 threshold 1. This verifies the
global weighted input. No compatibility with every auxiliary mollifier
quantity in the derivation of that input is asserted.

Use the tent of (1) of the block proof with any half-width
\(D_0/1000\le d<D_0\), and write \(s=c-c_0\). The interior location
window is \(|s|\le r=D_0-d\). Put
\[
 z=(H+W)D_0/2,\quad B_*=(1-z^2/6)^2,\quad
 B_j=\operatorname{sinc}^2(d\gamma_j/2),\quad
 A=2e^{(b-1)c_0}\sum_{j=1}^m B_j .
\]
Here \(z<1\), so \(B_j\ge B_*\) by the elementary sine series bound.
From the compact integral for \(K_d\),
\(|K_d(b-1+i\gamma_j)-B_j|\le e^d-1\).
Since all selected ordinates satisfy \(e^{i\gamma_j c_0}=1\), their
right-side contributions, including negative-height conjugates, obey
\[
 |Z_{\rm right}(c_0+s)-A\cos(Hs)|\le A\epsilon,\qquad
 \epsilon=e^{D_0}-1+e^{D_0}\big(WD_0+(e^{D_0}-1)/B_*\big).
\]
This follows term by term from \(|e^{i(\gamma_j-H)s}-1|\le W D_0\)
and the bounds on the variation of the real exponential and the tent
transform. Since \(HD_0<\pi/2\), direct integration gives
\(\frac1{2r}\int_{-r}^r\cos^2(Hs)\,ds\ge1/2\) for every \(r\) considered.
The root-mean-square of this group is therefore at least
\(2m e^{(b-1)c_0}B_*(2^{-1/2}-\epsilon)\).

For the remaining model points above \(H\), \(\beta\le1/2\).
Integrating the absolute tent bound against \(N(t)\le t\log t\) as
before, their combined absolute effect (including negative heights)
is at most
\[
  4e^{D_0-(c_0-D_0)/2}\,T_{\max}(\log T_{\max}+1),
  \qquad T_{\max}=2000/D_0\ge2/d .
\]
Subtract this in the root-mean-square inequality. Using the scalar Arb
checks in [check_single.py](check_single.py), the full model obeys
\[
 \frac1{2r}\int_{-r}^r |Z(c_0+s)|^2 ds >
 \begin{cases}8.06,&L=116,\\4.22,&L=120.\end{cases}
\]
In particular the available spectral upper inputs admit a larger energy
than the normalized empty-gap threshold 1, even on the centered window
of the individual gap, throughout a thousandfold range of tent widths.
The real prime measure has other constraints, including positivity in its
explicit formula. A proof using those constraints or a new estimate on
actual phase correlations would go beyond this countermodel.
