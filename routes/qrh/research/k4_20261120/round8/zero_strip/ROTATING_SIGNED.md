# Interchanging the target and boundary interval in a signed circle mean

Use the polynomial, normalized analytic function, target correction and parameters in [ROTATING.md](ROTATING.md). The improvement below applies to a nonoscillatory source. Write \(I=[H',T']\) for its positive target interval. To cover the point-dependent correction \(|c_0-1|\le\epsilon\), use the signed real majorant

\[
 A(z)=\log\big(|D(z)|+b(|z|)\big),\qquad
 b(v)=\sum_{k\ge2}|c_k|v^k((1+\epsilon)^k-1).
\]

Thus \(\log|D(c_0z)|\le A(z)\). The function \(A\) is subharmonic: it is the logarithm of the sum of absolute values of the analytic functions \(D(z)\) and the constant multiples of \(z^k\) in the pad. This follows from the submean inequality and Hölder, or from the supremum over constant phases of the log modulus of their linear combination. They never vanish simultaneously, so \(A\) is continuous. Its circular mean is convex in log radius. The same facts hold for \(A_+=\max(A,0)\). The sample bounds used for the positive circular mean in [ROTATING.md](ROTATING.md) apply also to \(A_+\) itself. Let \(c_s,C_s\) denote the upper circular constants for \(A,A_+\), respectively, after division by \(v^s\).

For the signed constant, use the same arc upper bound on \(|D|+b\) and take its logarithm before averaging. If \(v\le1/16\), all the polynomial roots lie outside its disk and the circular mean of \(\log|D|\) is exactly \(\log D(0)=0\) by Jensen. Moreover \(|D|\ge(1-v)(1-v/J)^J\ge(1-v)^2\). Consequently the signed mean is bounded by \(b(v)/(1-v)^2\). The large-radius bound and secant interpolation are unchanged. This proves \(c_{4/3}<0.285162\), \(c_2<0.185162\) for \(J=8\).

## Two interval indicators

At fixed edge ordinate \(u\), let \(v=u-t_0\), let \(k(v)\) be the normalized, even Poisson density of the chosen edge, and write \(A_u(v)=A(e^{i\lambda v}Y(u))\), where \(Y(u)\) is the corresponding scaled complex boundary value. Apply the strip submean inequality to the signed log modulus on the target line, with \(A_u\) as the upper boundary data. The switch from \(t_0\in I\) to \(u\in I\) obeys

\[
 \left|\iint [1_I(u-v)-1_I(u)]\,k(v) A_u(v)\,du\,dv\right|
 \le 2K\int |v|k(v)\,dv,
\]

provided \(|A_u(v)|\le K\) everywhere. This follows by integrating the symmetric difference of a finite interval and its translate. After the switch, the inner variable runs over the complete real line. Its folded circular density has pointwise distance at most \(e=W-1\) from one by the same Fourier calculation as in [ROTATING.md](ROTATING.md). For \(e<1\), its product with \(A\) is at most \((1-e)A+2eA_+\). The effective signed constant on that boundary is therefore \((1-e)c_s+2eC_s\).

For strip width \(w\) and boundary probability \(m\), the normalized density is at most \(e^{-\pi |v|/w}/[wm(1-e^{-\pi})^2]\) when \(|v|>w\), by the explicit strip Poisson kernel. Split at \(|v|=w\) to bound its first absolute moment by

\[
 w+\frac{2w e^{-\pi}(1+\pi)}{m\pi^2(1-e^{-\pi})^2}.
\]

Thus after weighting by the two probabilities and dividing by \(2\pi\), the complete exchange penalty is at most

\[
 \frac{K w}{\pi}\left(1+\frac{4e^{-\pi}(1+\pi)}{\pi^2(1-e^{-\pi})^2}\right).
\]

Only the boundary moments on \(u\in I\) are needed after the exchange. In a centered window they are bounded by the original positive half-axis masses. A translated window can use the full-axis bounds.

## Global majorant for the exchange

Allow a growth parameter \(V\ge25\), independent of the local logarithmic radius \(U\) used for the mollifier and the moments. Assume \(QX\le e^{3V}\), \(|C|+2R_0+3\le4e^V\), and \(.4\le\ell\le.5\), \(1<r<1.5\). On the left Euler summation at \(N=\lceil |u|+2\rceil\) bounds \(|\zeta(\ell+iu)|\le8(|u|+3)^{.6}\) using \(1/(1-\ell)\le2,\ 1/\ell\le2.5,\ |\ell+iu|\le N\). The mollifier coefficients have absolute value at most one and support at most \(QX\), hence \(|M|\le3(QX)^{.6}\). The normalized analytic window is bounded by \(\min(1,(1.01R_0/|u-C|)^{2048})\) and the pole remover has modulus at most one. This gives

\[
 |G(\ell+iu)|\le 1+24[(|C|+2R_0+3)QX]^{.6}<e^{4V}.
\]

Indeed for \(|u-C|>2R_0\), the ratio \((|u|+3)/(|C|+2R_0+3)\) is at most \(|u-C|/(2R_0)\), and the window absorbs it. The left radial multiplier is less than one. The right bound is \(|G(r+iu)|\le 1+(1+1/(r-1))^2\), by absolute Dirichlet convergence. The verifier checks that this times \(e^{\lambda(r-a)}\) is less than \(e^{4V}\).

For any resulting scaled modulus \(v\le e^{4V}\), the upper logarithm is at most \((J+1)(4V+2)\), by \(|c_k|\le\binom{J+1}k\). On \(v<1/4\) the factor bound \(|D|\ge(1-v)^2\) gives \(A>-1\). On \(v\ge1/4\), \(|c_2|=(J+1)/(2J)\ge1/2\), so \(b(v)\ge[(1+\epsilon)^2-1]/32>e^{-20}\). Hence \(K=(J+1)(4V+2)+20\) suffices.

Replacing each \(W C_s\) in (1) of [ROTATING.md](ROTATING.md) by the signed constant and adding the exchange penalty proves [rotating_signed.py](rotating_signed.py). Its returned value includes this penalty but still excludes the ordinary Green horizontal and right edges, for which \(J=8\) pays \(9/8\) times the archived allowance. The rate is balanced using \(c_p,c_q\), while \(L,R,r\) still use the local \(U\). At \(U=V=35,a=.865\) the resulting source with interval penalty is below 63,947.325, compared with the log-positive estimate 84,331.101 and the older radial estimate 153,122.698.

~~~powershell
python -Bu rotating_signed.py
~~~

The signed scalar means with the archived seven-taper table starting at log height 33 cover **\([128,135]\)** in 28 closed cells. The maximal original upper endpoint was smaller than **0.977419723165796**. Its constants used the arc estimates above. The current implementation also takes their minimum with the tighter [Jensen calculation](jensen_circle.py), which can change output in later replays.

~~~powershell
python -Bu rotating_bridge.py --first 128 --last 135 --pieces 28 --nh 6
~~~

2026-11-20. Joint project attribution to Claude and Codex.
