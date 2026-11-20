# Checking a closed high-real-part rectangle by interpolation

Take $H=3\,000\,175\,332\,800$, $c=67/80$, and $V=H+514$. The [verifier](zero_free_patch.py) checks $\zeta(\sigma+it)\ne0$ throughout $4/5\le\sigma\le7/8$, $H\le t\le H+L$, when it terminates with a positive modulus bound at the requested integer $L$. For $L=32$ the completed run used 431 complex zeta evaluations and covered the strip by 8,140 accepted boxes. The analytic interpolation remainder was below $4.474\,10^{-7}$, and the resulting minimum modulus bound exceeded $.00053650$. This tests a continuous strip of actual ordinates. The [first rectangle needed for closure](../kernel/GRID_TARGET.md) extends to $H e^{1/4}$. An individual local strip contributes only its own covered heights.

Use the explicitly smoothed finite polynomial $Z$ of the [Euler–Maclaurin estimate](../spectrum/COMPACT_EULER.md) at $M=V/4$. On $H-3\le t\le V$ and $4/5\le\sigma\le7/8$ that proof gives $|\zeta-Z|\le\delta<10^{-19}$ with $H-3$ used for the four pole integrations. Put $\Omega=\tfrac12\log(2M)$. For a cell $[t_0-1/24,t_0+1/24]$ define
\[
 F(w)=e^{i\Omega w} Z(c+i(t_0+w)).
\]
It is a finite exponential sum with angular frequencies $\Omega-\log n\in[-\Omega,\Omega]$. On $|w|=R=15/4$ it has modulus at most $C e^{\Omega R}$, $C=1+((2M)^{1-c}-1)/(1-c)$. This bound on the circle uses only the polynomial; the zeta approximation is needed at the interpolation nodes and in the target cell.

Interpolate at the 48 symmetric nodes $\pm a_j$, $a_j=(j+1/2)/12$, $j=0,\ldots,23$. They all lie inside that circle. On the whole target rectangle $w=(t-t_0)-i(\sigma-c)$ one has $|w|\le r=\sqrt{(3/80)^2+(1/24)^2}$. The contour remainder formula for Lagrange interpolation bounds the absolute error by
\[
 E=C e^{\Omega R}\frac R{R-r}
      \prod_{j=0}^{23}\frac{r^2+a_j^2}{R^2-a_j^2}<10^{-5}.
\]
Indeed the contour formula has the node polynomial $\prod(w^2-a_j^2)$ in the numerator and its value at the integration point in the denominator. The distance from the circle to $w$ is at least $R-r$.

The program evaluates $\zeta(c+i t)$ at the height nodes using 128-bit complex ball arithmetic. Enlarging both coordinates by $\delta$ encloses the sample of $Z$, after which the phase gives $F$. The normalized coordinate $24w$ puts the nodes at odd integers. The Lagrange basis numerators and denominators are computed as exact integers, then enclosed by Arb. Horner evaluation and recursive bisection cover each complete target rectangle. If $m$ is the interval lower bound on the local interpolation polynomial's modulus, the certified lower bound for $|\zeta|$ is $(m-E)e^{-\Omega r}-\delta$. A failed enclosure at the subdivision limit raises an error. The [complex-ball implementation](https://python-flint.readthedocs.io/en/latest/acb.html#flint.acb.zeta) is a numerical input to this local check.

~~~sh
python -B round5/low/zero_free_patch.py --length 32 --workers 3
~~~

## An independent Turing count across the same endpoint

Platt and Trudgian specify both $H$ and the last positive index $12\,363\,153\,437\,138$ through that height in Theorem 1. Starting at that index, the [batch verifier](turing_patch.py) used FLINT 3.6.0's Platt/Turing routine to isolate 2,048 consecutively indexed critical-line zeros. It checks the returned count, all interval orderings and that $H$ lies strictly between the first two intervals. The first ordinate is within $.000003$ of $3000175332799.93117$ and the last within $.000046$ of $3000175333278.3754$. Thus, joined to Theorem 1, the local computation places all nontrivial zeros of positive height up to **$3000175333278=H+478$** on the critical line. This full-strip result does not require QRH. The two checks have different validation arguments. [Platt–Trudgian, Theorem 1](https://arxiv.org/pdf/2004.09765) · [FLINT's Turing algorithm](https://flintlib.org/doc/algorithms/special-functions/zeta-zeros.html) · [Pinned batch routine](https://raw.githubusercontent.com/flintlib/flint/v3.6.0/src/acb_dirichlet/platt_hardy_z_zeros.c)

~~~sh
python -B round5/low/turing_patch.py
~~~

The default uses the public C interface in the 64-bit FLINT 3.6.0 wheel. The portable entry point uses python-flint's consecutively indexed zero routine. Both check the same ordering and endpoints.

2026-11-20. Joint project attribution to Claude and Codex. Codex developed these local checks.
