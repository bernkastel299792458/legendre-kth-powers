# Angular averaging on both boundary lines

Retain the finite-height rectangles, QRH, and arithmetic boundary estimates of [WEIGHTED_GREEN.md](WEIGHTED_GREEN.md). Write \(p=4/3,q=2\), \(\ell=1/2-h\) with \(0\le h<.1\), \(r=1+\delta/U\), \(a\in(\ell,r)\), \(A=a-\ell\), \(B=r-a\), \(w=A+B\), \(t=B/w\). The boundary moments below are the existing half-axis bounds \(L=e^U U^2 K_1\) and \(R=U K_3\) for the centered, conjugation-symmetric flat window. All source prices below include the Littlewood divisor \(2\pi\). This section concerns nonoscillatory scalar sources.

Use the bounded analytic strip function

\[
 G(z)=(1+10^{-6})^{-1}g(z)\frac{z-1}{z+2h}\, f(z),\quad f=\zeta M-1 .
\]

This scaling absorbs the flat window's upper factor on both moment boundaries. In a translated window centered at \(C\) with half-length \(R_0\), \(1/g(z)=1+((z-iC)/(1.01R_0))^{2048}\). In a centered window \(C=0,R_0=e^U\). Require \(((1+2/R_0)/1.01)^{2048}<10^{-7}\), which holds for \(R_0\ge10^6\). For a target point \(z_0=a+i t_0\) with \(|t_0-C|\le R_0\) and \(t_0>3\cdot10^{12}\), let \(c_0=(1+10^{-6})(z_0+2h)/[(z_0-1)g(z_0)]\). The triangle inequality and \((1+2h)/|z_0-1|<4\cdot10^{-13}\) give \(|c_0-1|<\epsilon=2\cdot10^{-6}\); the identity \(c_0G(z_0)=f(z_0)\) also holds at zeros. Holomorphy and decay of \(G\) are those in the flat-window proof. In particular the factor \(z-1\) cancels the true pole even in the translated version.

For the ordinary centered scalar rows frozen at $T$, the displaced horizontal edge can occur in $(T,T+.1]$. For $a<1.5$ and $t_0$ on the source interval, $|a+it_0|\le T+.1+a<T+2$. Thus the displayed $(1+2/T)$ allowance also proves the same correction bound when this displacement is used. The oscillatory Green rows choose their source slab at $\log(T+.1)$.

Choose \(1\le J\le8\) integral, \(D(z)=(1+z)(1-z/J)^J\). It has a simple zero at \(-1\), real coefficients, \(D(0)=1\), \(D'(0)=0\), and degree \(J+1\le9\). Writing \(D=\sum c_kz^k\), the verifier checks \(|c_k|\le\binom{J+1}{k}\) and the small-disk criterion in [RADIAL.md](../../round5/kernel/RADIAL.md). The later angular table uses a degree coefficient of eight in its Jensen integrand. Accordingly \(J=8\) pays **9/8 of the complete archived edge cap**. This dominates the required change in its nonnegative degree term and also pays the other edge terms. These edges refer to \(D(f)\), without an exponential rotation.

For every \(z_0\) apply strip subharmonicity to the bounded analytic function

\[
 D\big(c_0 e^{\lambda(z-z_0)}G(z)\big),\qquad \lambda>0 .
\]

At \(z_0\) the argument is exactly \(f(z_0)\). At the left edge \(z=\ell+iu\) its amplitude prior to \(c_0\) is \(v_L=e^{-\lambda A}|G(\ell+iu)|\); at the right it is \(v_R=e^{\lambda B}|G(r+iu)|\). Its new angle contains \(\lambda(u-t_0)\). Bound \(\log^+|D(c_0z)|\) by the common nonnegative majorant \(F(z)=\sup_{|c-1|\le\epsilon}\log^+|D(cz)|\). This eliminates the dependence of the complex correction on \(t_0\). The function \(F\) is continuous, subharmonic as a locally bounded maximum over a compact family, and conjugation symmetric.

After integration in \(t_0\) over the actual rectangle, positivity permits extending the majorant to the positive half-line. Equivalently extend using the reflected interval and divide the full-axis integral by two. At fixed edge ordinate \(u\), the averaging kernel in \(v=u-t_0\) is the normalized strip Poisson probability. When folded under \(v\mapsto\lambda v\pmod{2\pi}\), its Fourier coefficient at index \(k\) equals the normalized Poisson attenuation at \(|k|\lambda\). Its constant coefficient is one. On the left the other coefficients are bounded by \(e^{-|k|\lambda A}/[t(1-e^{-2|k|\lambda w})]\) and on the right interchange \((A,t)\) and \((B,1-t)\). The absolute Fourier series shows the densities with respect to normalized circular measure are bounded above by

\[
 W(x,m)=1+\frac{2e^{-\lambda x}}{m(1-e^{-\lambda x})(1-e^{-2\lambda w})}.
\]

Let \(C_s\) bound the circular mean of \(F(ve^{i\phi})/v^s\), uniformly in \(v>0\). Integrating first in \(t_0\), then in \(u\), gives the scalar source price

\[
 \frac1{2\pi}\left[t W(A,t) C_p L e^{-p\lambda A}+(1-t)W(B,1-t) C_q R e^{q\lambda B}\right]. \tag{1}
\]

For nonsymmetric translated windows, extend directly to the full \(t_0\)-axis and use full-axis moment bounds \(L,R\) in (1). A table storing one half of those full-axis bounds must be doubled on both edges. The proof needs no symmetry in this version. A positive rate that balances the terms before the harmless wrapped-density factors is \(\log(p C_p L/(q C_q R))/(pA+qB)\).

## Circle and edge constants

On each of the 257 radii of [shared_radial.py](shared_radial.py) divide the upper semicircle into 384 equal arcs. The logarithm of \(|D(re^{i\phi})|\) is concave in \(x=\cos\phi\) and maximized at \(-(1-1/J)r/2\) clipped to the arc's cosine range; differentiation of the two linear logarithms gives this point. At the arc maximum add \(\sum_{k\ge2}|c_k|r^k((1+\epsilon)^k-1)\) to the modulus to cover every admissible complex multiplier, then take \(\log^+\). For \(r\le1/16\) use \(\log|1+w|\le\Re w+|w|^2/2\). The unperturbed quadratic positive part has circular mean \(|c_2|r^2/\pi\), and the code explicitly adds the perturbed quadratic coefficient, the absolute higher coefficients, and the square remainder. For \(r\ge16\) the log sum of absolute coefficients plus \((J+1)\log(r/16)\) bounds the integrand; the quotient by \(r^s\) decreases there. The true circular mean of the subharmonic \(F\) is convex in \(\log r\), so the same exponential secant factor as in [SHARED_RADIAL.md](SHARED_RADIAL.md) fills every intervening radius.

For \(J=8\), [rotating.py](rotating.py) proves \(C_{4/3}<0.372687331\), \(C_2<0.247296233\). At \(U=35\) and \(a=.80,.85,.865,.874\), the rotating prices divided by the old radial prices on the same taper and auxiliary line are respectively below \(.569885,.558693,.550742,.552069\), before adding the common edge. The representative arbitrary-height comparator and both constants can be recomputed in this directory:

~~~powershell
python -Bu rotating.py
~~~

With the original spatial polygon, the positive circular means establish **\([135,137.25]\)** in nine closed cells. The upper endpoint, including the \(9/8\) angular table allowance, is smaller than **0.743760762910586**.

~~~powershell
python -Bu complete_green.py --first 135 --last 137.25 --pieces 9 --uniform 3 --nh 6 --sub 16 --hi 41 --step 4 --shift-rows phase_shift_extra.json --shifts '.012,.016' --rotate-scalar
~~~

2026-11-20. Joint project attribution to Claude and Codex.
