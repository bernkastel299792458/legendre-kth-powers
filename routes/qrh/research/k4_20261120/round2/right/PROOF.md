# Centered Barban–Vehov coefficients and fourth powers for \(\log x\ge267\)

Assume QRH(7/8) and the analytic inputs of the [first-round upper proof](../../upper/PROOF.md), including the fourth-moment estimates in the fixed Chourasiya–Simonič v2 preprint. With the explicit Möbius estimates specified below, every real \(x\ge e^{267}\) has a prime in \((x,x+4x^{3/4})\). At \(L=267\) the full normalized budget is below \(0.983654\). This is a written conditional proof with an Arb check of its scalar inequalities. It leaves smaller fourth-power intervals to the other parts of the project.

Fix \(U_0=64,\ T_0=e^{64},\ A_0=e^{58},\ H=3\cdot10^{12},\ W=9.25,\ h=e^{-2.45},\ \delta=.65,\ \kappa=.105\). For \(T\ge T_0\) put \(U=\log T,\ Y=hT,\ X=e^W Y,\ Y_0=hT_0,\ e_0=2\delta/U_0,\ e=2\delta/U\). Let \(\omega(d)=1\) for \(d\le Y\), \(\omega(d)=\log(X/d)/W\) for \(Y<d<X\), and \(\omega(d)=0\) for \(d\ge X\). Write \(M(z)=\sum_d\mu(d)\omega(d)d^{-z}\) and \(f=\zeta M-1\).

## 1. A scalar bound for the centered coefficient norm

For \(v>1\), put \(S(v)=\sum_n |\sum_{d\mid n}\mu(d)(1-\omega(d))|^2 n^{-v}\). The inner coefficient is the negative of the Dirichlet coefficient of \(f\), also at \(n=1\). In particular it vanishes through \(Y\). Define \(b(j)=\sum_m\mu(m)m^{-v}(1-\omega(jm))\). Then
\[
 S(v)\le\zeta(v)\sum_{j\ge1}j^{-v}b(j)^2.                         \tag{1}
\]
Indeed expand using \([d_1,d_2]^{-v}=(d_1d_2)^{-v}\sum_{q\mid(d_1,d_2)}J_v(q)\), with \(J_v(q)=q^v\prod_{p\mid q}(1-p^{-v})\). This gives \(S(v)/\zeta(v)\) as the sum over squarefree \(q\) of \(q^{-v}\prod_{p\mid q}(1-p^{-v})\) times
\[
 \left|\sum_{(m,q)=1}\mu(m)m^{-v}(1-\omega(qm))\right|^2
 =\left|\sum_{k\mid q^\infty}k^{-v}b(qk)\right|^2 .
\]
The equality uses the convolution of \(\mu\) with the indicator of the integers supported on primes dividing \(q\). Cauchy–Schwarz costs the reciprocal product \(\sum_{k\mid q^\infty}k^{-v}\). The remaining sum enumerates \(j=qk\) exactly once with \(q=\operatorname{rad}(j)\), including \(q=j=1\). All expansions are absolute since \(v>1\), the coefficients are bounded by divisor functions and \(\sum d(n)^2n^{-v}<\infty\).

Let \(r(t;v)=\sum_{m>t}\mu(m)m^{-v}\). Averaging a sharp cut in logarithmic scale gives the exact identity
\[
 b(j)=W^{-1}\int_Y^X r(z/j;v)\,dz/z .                         \tag{2}
\]

### The norm at \(v=1+e\)

Write \(m(t)=\sum_{n\le t}\mu(n)/n\), \(N=2048\), \(C=.011\). For \(t\ge1\),
\[
 |m(t)|\le M_0(t)+C/(1+\log t),\qquad
 M_0(t)=\begin{cases}|m(\lfloor t\rfloor)|,&1\le t<N,\\
                       \sqrt{2/t},&t\ge N.\end{cases}
\]
For \(t\le10^{14}\) this follows from Helfgott's finite verification. For \(t>10^{14}\), \(0.010032/\log t\le C/(1+\log t)\) by Ramaré and Zuniga-Alterman. [Helfgott, Lemma 5.10](https://webusers.imj-prg.fr/~harald.helfgott/anglais/PartI.pdf) and [Ramaré–Zuniga-Alterman, Corollary 1.2](https://arxiv.org/html/2408.05969v2).

For \(j\le Y\), put \(s=\log(Y/j)\), \(A(s)=\int_s^\infty M_0(e^z)\,dz\). Abel summation gives \(r(e^t;1+e)=-e^{-et}m(e^t)+e\int_t^\infty e^{-ez}m(e^z)\,dz\). In (2), the first \(M_0\) integral costs at most \(e^{-es}A(s)\), the second at most \(eW e^{-es}A(s)\) after interchanging integrals. Both \(C\) terms separately cost at most \(C W e^{-es}/(1+s)\). Thus
\[
 |b(j)|\le e^{-es}\left[(1+e_0W)A(s)/W+2C/(1+s)\right].          \tag{3}
\]
In bounding the contribution to (1), \(j^{-e}e^{-2es}\le Y^{-e}\). The script certifies \(\sum_{j\le Y}A(s)^2/j\le E<1.099\) uniformly. For \(Y/(n+1)<j\le Y/n,\ n=1,\ldots,N-1\), the squared bound uses
\[
 A(s)\le A_n=\sqrt{8/N}+\sum_{i=n}^{N-1}|m(i)|\log(1+1/i),
 \qquad\sum_{Y/(n+1)<j\le Y/n}\frac1j\le\log(1+1/n)+(n+1)/Y_0 .
\]
For \(j\le Y/N\), \(A(s)^2=8j/Y\) and the contribution is at most \(8/N\). Also \(\sum_{j\le Y} [j(1+s)^2]^{-1}\le V_0=1+(1+\log Y_0)^{-2}+1/Y_0\). Its continuous integral is below 1, and the summand decreases then increases as a function of \(j\), so the two endpoint values suffice for the sum–integral comparison. By the triangle inequality in weighted \(L^2\), the contribution of \(j\le Y\) to \(\sum j^{-v}b(j)^2\) is at most \(Y^{-e}B_0\) with \(B_0=[(1+e_0W)\sqrt E/W+2C\sqrt{V_0}]^2\).

For \(Y<j\le X\), put \(z=X/j\ge1\). Then \(b(j)=1/\zeta(1+e)-G(z)/W\), where \(G(z)=\sum_{m\le z}\mu(m)m^{-1-e}\log(z/m)\). The primary estimate \(0\le G(z)\le1.00303(1+e\log z)\), together with \(e/(1+e)\le1/\zeta(1+e)\le e\), yields \(|b(j)|\le B_1=\max(e_0,1.00303/W+e_0[.00303+e_0/(1+e_0)])\). The sum of weights \(j^{-v}\) in this range is at most \(Y^{-e}(W+1/Y_0)\). [Ramaré–Zuniga-Alterman, Lemma 3.1 with \(q=k=1\)](https://arxiv.org/pdf/2405.12662).

For \(j>X\), \(b(j)=1/\zeta(1+e)\). This tail after multiplication by \(\zeta(1+e)\) is at most \(Y^{-e}(1+e_0/Y_0)\) by integral comparison, including the endpoint rounding. Since \(Y^{-e}\le D=e^{-2\delta}h^{-e_0}\), the bound used in the script is
\[
 S(1+e)/U\le D\left[(1/U_0+1/(2\delta))
    \{B_0+(W+1/Y_0)B_1^2\}+(1+e_0/Y_0)/U_0\right]=C_{\rm low}.
                                                                    \tag{4}
\]

### The norm at \(v=2+e\)

Write \(d=v-1\ge1\). For \(t\ge1\), integral comparison gives \(|r(t;v)|\le 2t^{-d}\). For \(j\le Y\), (2) gives \(|b(j)|\le2(j/Y)^d/W\), so their weighted contribution in (1) before multiplying by \(\zeta(v)\) is at most \(Y^{-d}(4/W^2)(1+1/Y_0)\).

For \(j>Y\) put \(u=\log(j/Y)\). Then \(|b(j)|\le (u+1)/W\), since the part of (2) below \(t=1\) has integrand \(1/\zeta(v)\le1\), and \(\int_1^\infty |r(t;v)|\,dt/t\le\sum_{m\ge2}(\log m)/m^2<1\). The final inequality follows by summing \(m=2,3\) and integrating the decreasing summand from 3. This bound also holds for \(j>X\). The function \(t^{-1-d}(1+\log(t/Y))^2\) decreases for \(t\ge Y\), and its integral there is at most \(5Y^{-d}\). Including a first endpoint gives \(Y^{-d}(5+1/Y_0)/W^2\). Since \(\zeta(v)<2\), we obtain
\[
  T S(2+e)\le 2Dh^{-1}(9+5/Y_0)/W^2=C_{\rm high}.                \tag{5}
\]

## 2. Boundary moments for the same mollifier

Use the real-coefficient mean-value inequality obtained by applying (49) of CS v2 on \([-V,V]\) and dividing by 2. To place the interval in its stated positive domain, translate to \([1,1+2V]\) and multiply each coefficient by the corresponding unimodular phase. Returning to the original real coefficients restores symmetry about zero. Absolute convergence and the finite weighted norms justify the limit for \(f\) on the right vertical line. With \(m_0=\sqrt{1+\frac23\sqrt{6/5}}\) this gives
\[
 \int_0^V |f(1+\delta/U+it)|^2dt
 \le \pi m_0 S(1+e)+(V+\pi m_0/2) S(2+e).
\]
In the right endpoint of CS (30), \(V=T\sqrt{u/(2\kappa)}\) is integrated against \(e^{-u}du\) on \([0,\infty)\). Equations (4) and (5) bound this by \(K_3U\), with
\[
 K_3=\pi m_0 C_{\rm low}
  + [\sqrt\pi/(2\sqrt{2\kappa})+\pi m_0/(2T_0)] C_{\rm high}/U_0.
\]
[Chourasiya–Simonič v2, (30), (49)](https://arxiv.org/html/2507.15184v2).

On the critical line the real-coefficient bound gives \(\int_0^V|M(1/2+it)|^2dt\le(c_1 V+c_2T)U\). To see this, write \(P=2\cdot3\cdot5\cdot7\cdot11\), \(b=\sum_{d\mid P}\mu(d)/d^2\), \(c=\sum_{d\mid P}[\max(\mu(d),0)-2\mu(d)\log d]/d^2\). Inclusion–exclusion for the restrictions \(p^2\nmid n\ (p\mid P)\) gives \(\sum_{n\le X}\mu^2(n)/n\le b\log X+c\), using \(\log t\le H_{\lfloor t\rfloor}\le1+\log t\) for \(t\ge1\); here \(X>P^2\). The same restrictions give \(\sum_{n\le t}\mu^2(n)\le bt+16\). Partial summation against decreasing \(\omega^2\) now gives \(\sum_n\mu^2(n)\omega(n)^2\le 2bX/W^2+16\), using \(\int_0^X\omega(t)^2dt\le2X/W^2\). Hence
\[
 c_1=b+[b(W+\log h)+c]/U_0,\qquad
 c_2=\pi m_0[(2bhe^W/W^2+16/T_0)/U_0+c_1/(2T_0)].
\]
The interpolation theorem applies to this \(f\) exactly as in the proof of CS Corollary 6 by Theorem 4: for each fixed \(T\) the Dirichlet polynomial is fixed, has real coefficients, and \(f\) has at most the simple pole at 1 and polynomial vertical growth. The left Hölder estimate preceding CS (42) uses only the displayed critical-line mean and CS Corollary 5 for \(\zeta\); therefore CS (37),(38) hold with these \(c_1,c_2\) in place of their respective coefficients for \(h=1\).

The script uses the same exponential tangent for (37) as in the first round. After that tangent the integral is bounded by \(D_0\int_0^\infty u^{1/6}e^{-(1-c_0)u}(c_1\sqrt{au}+c_2)^{2/3}du\), with \(a,c_0,D_0\) defined in [the first-round proof, §1](../../upper/PROOF.md). Normalizing the gamma density and applying Jensen to the concave \(2/3\)-power gives the integral bound
\[
 D_0\frac{\Gamma(7/6)}{(1-c_0)^{7/6}}
 \left[c_1\sqrt a\,\frac{\Gamma(5/3)}{\sqrt{1-c_0}\Gamma(7/6)}+c_2\right]^{2/3}.
\]
The finite \(A_0\) contribution in (37) is retained. The resulting uniform bounds are \(K_1<2.87649,\ K_2<2.98418,\ K_3<0.164303\). The right-line shift is \(1+\delta/\log T\), and all powers in the first-round chord argument use \(\log T\), including for this longer polynomial.

## 3. Littlewood boundaries and infinite-range certificate

Use the same \(D_5(f)=(1+f)(1-f/5)^5\) and \(s\)-knots as [the first-round proof, §§2–4](../../upper/PROOF.md). On \(\Re z=2\) all Dirichlet coefficients of \(f\) through \(Y\) vanish and the others are bounded in modulus by \(d(n)\). Thus \(|f|\le9/\sqrt Y\). The cost of the right edge is at most \(162/h\). On either Jensen disk the simple estimate for the longer \(M\) is \(2\sqrt X\), giving outer modulus at most \((11\sqrt{he^W})^6 T^9\). The disk radii, detector bounds and other terms remain exactly as in that proof.

To take rectangular endpoint limits at a fixed altitude \(T\), first **freeze \(Y,X,\omega\) at that \(T\)**. Choose generic \(T_j\downarrow T\), and \(H_j\downarrow H\) below the exact verified RH endpoint. These avoid the ordinates of the zeros of this fixed detector. A generic left-edge sequence tends to \(s\). The rectangle formula bounds the first integral by the integral of \(\log|D_5(f)|\) over that vertical edge. For this fixed holomorphic function it converges to the integral on \([H,T]\) at \(s\): in a compact neighborhood it factors into finitely many linear zero factors and a nonvanishing analytic factor; \(\log|\cdot|\) on each vertical segment for each zero factor has a continuous integral, including at its endpoints (the integral of \(|\log |t||\) over a shrinking interval tends to zero uniformly under a small lateral shift). The right integral and the explicit Jensen bounds likewise pass to the limit. Equivalently, at fixed \(s\) one can bound the integrand by the continuous \(J(|f|)\) before taking these limits. The majorant \(J(|f(z)|)\) is jointly continuous on the compact rectangles and so needs no logarithmic limiting argument. After the limit the moment estimate from §2 applies at **the original** \(T\); it is unnecessary to use the parameters \(Y=hT_j\) or a moving detector at a generic top. The Jensen disks before the limit remain bounded using \(4T_j\) and \(2\sqrt X\). Right zeros at \(\gamma=T\) are included by the downward top limit; no positive-distance zeros disappear below \(H_j\) by finite-height RH.

The script [verify_bv.py](verify_bv.py) uses the taper for every cumulative height \(T\) as required; its parameters do not depend on \(L\). The first-round positive hinge coefficients, normalized trapezoidal interval kernel, and fixed-height-measure comparison extend the strict budget from \(267\) to every \(L\ge267\). The code checks \(u_1=\log[(16/7)(1+e^{267/4}/4)]>64\), each logarithmic decay bound and the prime-power and trivial-zero terms. The resulting upper-bound expression is below \(0.983654\). Substituting \(x=n^4\) gives the prime strictly between consecutive fourth powers since the taper has zero weight at both ends.

Reproduce using Python with python-flint, from this directory:

```text
python -B verify_bv.py
```

At \(266\) this particular upper-bound expression is larger than \(1.01712\). No conclusion for that altitude follows from this comparison. The downstream estimates are not formalized in Lean. The approach was developed by Codex on the QRH route, with Claude's earlier chord estimate and the joint project attribution retained.
